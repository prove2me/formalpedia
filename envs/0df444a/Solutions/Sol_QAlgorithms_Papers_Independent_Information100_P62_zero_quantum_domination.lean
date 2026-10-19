-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.zero_quantum_domination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:52:52.599782+00:00
-- url     : https://prove2.me/submissions/d790b2e4-dd99-4c53-833e-1585d2af9a40

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_embedding_packing

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma projection_frame {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : IsProjection P) (d : ℕ) (hd : P.rank = d) :
    ∃ V : Matrix I (Fin d) ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = P := by
  classical
  let C := imageSpace P
  have hdim : Module.finrank ℂ C = d := by
    rw [← hd, Matrix.rank_eq_finrank_range_toLin P
      (EuclideanSpace.basisFun I ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
    rfl
  let b : OrthonormalBasis (Fin d) ℂ C :=
    (stdOrthonormalBasis ℂ C).reindex (finCongr hdim)
  let V : Matrix I (Fin d) ℂ := fun i a => (b a : EuclideanSpace ℂ I) i
  have hV : Vᴴ * V = 1 := by
    ext a c
    have hh := orthonormal_iff_ite.mp b.orthonormal a c
    rw [← inner_matrix_col_col]
    change inner ℂ (b a : EuclideanSpace ℂ I) (b c : EuclideanSpace ℂ I) = _
    simpa only [Submodule.coe_inner, Matrix.one_apply] using hh
  have hfix (x : C) : Matrix.toEuclideanLin P x = x := by
    obtain ⟨y,hy⟩ := x.property
    rw [← hy]
    have hh := congrArg (fun M => Matrix.toEuclideanLin M y) hP.2
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hh
  have hs : Matrix.toEuclideanLin P = C.starProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    symm
    apply (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (show Matrix.toEuclideanLin P x ∈ C from ⟨x,rfl⟩) ?_)
    intro y hy
    have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.1) x y
    have hfy := hfix ⟨y,hy⟩
    rw [inner_sub_left, hsym, hfy, sub_self]
  have hPV : V * Vᴴ = P := by
    calc
      V * Vᴴ = ∑ a, Matrix.vecMulVec (b a : EuclideanSpace ℂ I)
          (star (b a : EuclideanSpace ℂ I)) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
          Matrix.vecMulVec_apply, Pi.star_apply]
        rfl
      _ = Matrix.toEuclideanLin.symm C.starProjection.toLinearMap := by
        rw [b.starProjection_eq_sum_rankOne]
        simp only [ContinuousLinearMap.toLinearMap_sum, map_sum,
          InnerProductSpace.symm_toEuclideanLin_rankOne]
      _ = P := by rw [← hs]; simp
  exact ⟨V,hV,hPV⟩

private lemma frame_projection {I D : Type} [Fintype I] [Fintype D]
    [DecidableEq I] [DecidableEq D] (V : Matrix I D ℂ) (hV : Vᴴ * V = 1) :
    IsProjection (V * Vᴴ) ∧ (V * Vᴴ).rank = Fintype.card D := by
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  · rw [Matrix.rank_self_mul_conjTranspose,
      ← Matrix.rank_conjTranspose_mul_self V, hV, Matrix.rank_one]

private lemma graph_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : Superop I O) (hF : IsChannel F) : (1 : Matrix I I ℂ) ∈ graph F := by
  obtain ⟨r,E,hE,hEq⟩ := hF
  rw [← hE]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.subset_span ⟨r,E,hE,hEq,a,a,rfl⟩

private lemma feasible_bound {I : Type} [Fintype I] [DecidableEq I]
    (S : Submodule ℂ (Matrix I I ℂ)) (hS : (1 : Matrix I I ℂ) ∈ S)
    {m : ℕ} (v : Fin m → EuclideanSpace ℂ I)
    (hv : ∀ i, IsState (v i))
    (ho : ∀ i j, i ≠ j → ∀ X ∈ S, inner ℂ (v i) (act X (v j)) = 0) :
    m ≤ Fintype.card I := by
  have hn : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    split_ifs with h
    · subst j
      rw [inner_self_eq_norm_sq_to_K, hv i]
      norm_num
    · simpa [act] using ho i j h 1 hS
  simpa using hn.linearIndependent.fintype_card_le_finrank


private abbrev col {I : Type} (v : EuclideanSpace ℂ I) : Matrix I (Fin 1) ℂ :=
  fun i _ => v i

private lemma col_inner {I : Type} [Fintype I]
    (u v : EuclideanSpace ℂ I) (X : Matrix I I ℂ) :
    (col u)ᴴ * X * col v = (inner ℂ u (act X v)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a; subst b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, col,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    EuclideanSpace.inner_eq_star_dotProduct, act, dotProduct, Matrix.mulVec]
  simp only [Finset.sum_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma col_isometry {I : Type} [Fintype I] [DecidableEq I] (v : EuclideanSpace ℂ I)
    (hv : IsState v) : (col v)ᴴ * col v = 1 := by
  change ‖v‖ = 1 at hv
  have h := col_inner v v (1 : Matrix I I ℂ)
  simp only [Matrix.mul_one, act, Matrix.one_mulVec, WithLp.toLp_ofLp,
    inner_self_eq_norm_sq_to_K, hv, RCLike.ofReal_one, one_pow, one_smul] at h
  exact h

private lemma col_code {I : Type} [Fintype I] [DecidableEq I]
    (S : Submodule ℂ (Matrix I I ℂ)) (v : EuclideanSpace ℂ I) (hv : IsState v) :
    Code S (col v * (col v)ᴴ) ∧ (col v * (col v)ᴴ).rank = 1 := by
  obtain ⟨hP,hr⟩ := frame_projection (col v) (col_isometry v hv)
  refine ⟨⟨hP, ?_⟩, by simpa using hr⟩
  intro X _
  refine ⟨inner ℂ v (act X v), ?_⟩
  calc
    _ = col v * ((col v)ᴴ * X * col v) * (col v)ᴴ := by simp [Matrix.mul_assoc]
    _ = _ := by rw [col_inner]; simp [Matrix.mul_smul, Matrix.smul_mul]

private lemma classical_valid (m : ℕ) (hm : 0 < m) : Valid (classical m) := by
  constructor
  · intro h
    have := congrArg Multiset.card h
    simp [classical, equalBlocks] at this
    omega
  · intro d hd
    have : d = 1 := Multiset.eq_of_mem_replicate hd
    omega

private lemma classical_size (m : ℕ) (k : Block (classical m)) :
    blockSize (classical m) k = 1 :=
  Multiset.eq_of_mem_replicate (Multiset.mem_toList.mp (List.get_mem _ _))

private lemma feasible_transmits {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) {m : ℕ} (hm : 0 < m)
    (v : Fin m → EuclideanSpace ℂ I) (hv : ∀ i, IsState (v i))
    (ho : ∀ i j, i ≠ j → ∀ X ∈ graph F, inner ℂ (v i) (act X (v j)) = 0) :
    Transmits F (classical m) := by
  classical
  let idx : Block (classical m) → Fin m :=
    fun k => ⟨k.val, by simpa [classical, equalBlocks] using k.isLt⟩
  have hi : Function.Injective idx := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k => k.val) h
  apply (orthogonal_codes F hF _ (classical_valid m hm)).mpr
  refine ⟨fun k => col (v (idx k)) * (col (v (idx k)))ᴴ, ?_, ?_⟩
  · intro k
    simpa only [classical_size] using col_code (graph F) (v (idx k)) (hv _)
  · intro k j hkj X hX
    calc
      _ = col (v (idx k)) * ((col (v (idx k)))ᴴ * X * col (v (idx j))) *
          (col (v (idx j)))ᴴ := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [col_inner, ho _ _ (fun h => hkj (hi h)) X hX]; simp

private lemma codes_feasible {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A)
    (hsize : ∀ k : Block A, blockSize A k = 1) :
    ∃ v : Block A → EuclideanSpace ℂ I, (∀ i, IsState (v i)) ∧
      ∀ i j, i ≠ j → ∀ X ∈ graph F, inner ℂ (v i) (act X (v j)) = 0 := by
  classical
  obtain ⟨P,hP,ho⟩ := (orthogonal_codes F hF A hA.1).mp hA
  choose W hW hWW using fun k => projection_frame (P k) (hP k).1.1 1
    ((hP k).2.trans (hsize k))
  let v (k : Block A) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => W k i 0)
  have hc (k : Block A) : col (v k) = W k := by
    ext i j
    have : j = 0 := Subsingleton.elim _ _
    subst j; rfl
  have hv (k : Block A) : IsState (v k) := by
    have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) (hW k)
    rw [← hc] at hh
    have hh' := col_inner (v k) (v k) (1 : Matrix I I ℂ)
    simp only [Matrix.mul_one, act, Matrix.one_mulVec, WithLp.toLp_ofLp] at hh'
    rw [hh'] at hh
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      inner_self_eq_norm_sq_to_K] at hh
    have hr : ‖v k‖ ^ 2 = (1 : ℝ) := by
      have ht := congrArg (RCLike.re (K := ℂ)) hh
      simpa only [← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.one_re] using ht
    change ‖v k‖ = 1
    nlinarith [norm_nonneg (v k)]
  refine ⟨v,hv,?_⟩
  intro k j hkj X hX
  have h := ho k j hkj X hX
  have hwk : (W k)ᴴ * P k = (W k)ᴴ := by
    rw [← hWW k, ← Matrix.mul_assoc, hW k, Matrix.one_mul]
  have hwj : P j * W j = W j := by
    rw [← hWW j, Matrix.mul_assoc, hW j, Matrix.mul_one]
  have hh := congrArg (fun M => (W k)ᴴ * M * W j) h
  simp only [← Matrix.mul_assoc, hwk, Matrix.mul_zero, Matrix.zero_mul] at hh
  rw [Matrix.mul_assoc ((W k)ᴴ * X), hwj] at hh
  rw [← hc k, ← hc j, col_inner] at hh
  have hz := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hh
  simpa using hz

private lemma alpha_feasible {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I]
    (F : Superop I O) (hF : IsChannel F) :
    0 < alpha (graph F) ∧
    ∃ v : Fin (alpha (graph F)) → EuclideanSpace ℂ I, (∀ i, IsState (v i)) ∧
      ∀ i j, i ≠ j → ∀ X ∈ graph F, inner ℂ (v i) (act X (v j)) = 0 := by
  classical
  let S := graph F
  let s : Set ℕ := {m | ∃ v : Fin m → EuclideanSpace ℂ I, (∀ i, IsState (v i)) ∧
    ∀ i j, i ≠ j → ∀ X ∈ S, inner ℂ (v i) (act X (v j)) = 0}
  have hone : 1 ∈ s := by
    refine ⟨fun _ => ket (Classical.arbitrary I), ?_, ?_⟩
    · intro i; simp [IsState,ket]
    · intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  have hb : BddAbove s := ⟨Fintype.card I, by
    rintro m ⟨v,hv,ho⟩; exact feasible_bound S (graph_one F hF) v hv ho⟩
  have hp : 1 ≤ sSup s := le_csSup hb hone
  have hmem : sSup s ∈ s := Nat.sSup_mem ⟨1,hone⟩ hb
  exact ⟨hp, hmem⟩

private lemma no_large_code {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (F : Superop I O)
    (hz : quantumCapacity F = 0) (P : Matrix I I ℂ) (hP : Code (graph F) P) :
    P.rank ≤ 1 := by
  classical
  have hb : BddAbove {d | ∃ Q : Matrix I I ℂ, Code (graph F) Q ∧ Q.rank = d} :=
    ⟨Fintype.card I, by rintro d ⟨Q,_,rfl⟩; exact Matrix.rank_le_card_width Q⟩
  have hle : P.rank ≤ alphaQ (graph F) := le_csSup hb ⟨P,hP,rfl⟩
  by_contra hn
  have htwo : 2 ≤ alphaQ (graph F) := by omega
  have hreal : (1 : ℝ) < (alphaQ (graph F) : ℝ) := by exact_mod_cast (show 1 < alphaQ (graph F) by omega)
  have hlog := Real.log_pos hreal
  have hpos : 0 < quantumCapacity F := div_pos hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [hz] at hpos
  exact (lt_irrefl _ hpos)

theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (hzero : quantumCapacity F = 0) :
    Dominating F (classical (alpha (graph F))) := by
  classical
  obtain ⟨ha,v,hv,ho⟩ := alpha_feasible F hF
  refine ⟨feasible_transmits F hF ha v hv ho, ?_⟩
  intro B hB
  obtain ⟨P,hP,_⟩ := (orthogonal_codes F hF B hB.1).mp hB
  have hs (k : Block B) : blockSize B k = 1 := by
    have hle := no_large_code F hzero (P k) (hP k).1
    rw [(hP k).2] at hle
    have hp : 0 < blockSize B k := hB.1.2 _ (Multiset.mem_toList.mp (List.get_mem B.toList k))
    omega
  obtain ⟨w,hw,hwo⟩ := codes_feasible F hF B hB hs
  have hb : BddAbove {m | ∃ v : Fin m → EuclideanSpace ℂ I, (∀ i, IsState (v i)) ∧
      ∀ i j, i ≠ j → ∀ X ∈ graph F, inner ℂ (v i) (act X (v j)) = 0} :=
    ⟨Fintype.card I, by rintro m ⟨v,hv,ho⟩; exact feasible_bound _ (graph_one F hF) v hv ho⟩
  have hlen : B.toList.length ≤ alpha (graph F) := le_csSup hb ⟨w,hw,hwo⟩
  let f : Block B → Block (classical (alpha (graph F))) :=
    fun k => ⟨k.val, by have := Nat.lt_of_lt_of_le k.isLt hlen; simpa [classical,equalBlocks] using this⟩
  have hfi : Function.Injective f := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k => k.val) h
  apply (embedding_packing _ _ hB.1 (classical_valid _ ha)).1.mpr
  refine ⟨f, ?_⟩
  intro j
  rw [classical_size]
  simp only [hs, Finset.sum_const, smul_eq_mul, mul_one]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact hfi ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)

#print axioms solution
