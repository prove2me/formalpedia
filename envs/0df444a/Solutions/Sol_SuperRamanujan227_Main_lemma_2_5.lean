-- Prove2me | solution 1 for SuperRamanujan227.Main.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T01:22:38.673659+00:00
-- url     : https://prove2.me/submissions/8a7c27ec-d3e6-4cfe-85d0-d8efb7f29fb7

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_FiniteFreeConvolution
import Theorems.Thm_SuperRamanujan227_Main_lemma_2_2

open Polynomial Matrix Finset BigOperators Filter Topology

namespace SuperRamanujan227.Main

/-! ### Section 1: Real-rooted polynomial tools and coefficientwise limits -/

section RealRootedTools

lemma realRooted_one : RealRooted (1 : ℝ[X]) := by
  refine ⟨one_ne_zero, ?_⟩
  simp

lemma realRooted_X : RealRooted (X : ℝ[X]) := by
  refine ⟨Polynomial.X_ne_zero, ?_⟩
  simp

lemma realRooted_X_sub_C (c : ℝ) : RealRooted (X - C c) := by
  refine ⟨Polynomial.X_sub_C_ne_zero c, ?_⟩
  simp

lemma realRooted_of_mul {p q : ℝ[X]} (hr : RealRooted (p * q)) :
    RealRooted p ∧ RealRooted q := by
  have hp : p ≠ 0 := left_ne_zero_of_mul hr.1
  have hq : q ≠ 0 := right_ne_zero_of_mul hr.1
  have hcard : (p * q).roots.card = p.roots.card + q.roots.card := by
    rw [Polynomial.roots_mul hr.1, Multiset.card_add]
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree :=
    Polynomial.natDegree_mul hp hq
  have hle_p : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  have hle_q : q.roots.card ≤ q.natDegree := Polynomial.card_roots' q
  have heq := hr.2
  rw [hcard, hdeg] at heq
  exact ⟨⟨hp, by omega⟩, ⟨hq, by omega⟩⟩

lemma realRooted_mul {p q : ℝ[X]} (hp : RealRooted p) (hq : RealRooted q) :
    RealRooted (p * q) := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp.1 hq.1
  refine ⟨hpq, ?_⟩
  rw [Polynomial.roots_mul hpq, Multiset.card_add, Polynomial.natDegree_mul hp.1 hq.1, hp.2, hq.2]

lemma monic_eq_prod_roots_of_realRooted' {p : ℝ[X]} (hm : p.Monic) (hr : RealRooted p) :
    p = (p.roots.map (fun r => X - C r)).prod := by
  have hsplit : p.Splits := Polynomial.splits_iff_card_roots.mpr hr.2
  have h := hsplit.eq_prod_roots
  rw [hm.leadingCoeff, C_1, one_mul] at h
  exact h

lemma abs_le_one_add_sum_coeff_of_isRoot' {p : ℝ[X]} (hm : p.Monic) {r : ℝ}
    (hr : p.IsRoot r) :
    |r| ≤ 1 + ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
  by_cases h1 : |r| ≤ 1
  · have hnn : 0 ≤ ∑ j ∈ Finset.range p.natDegree, |p.coeff j| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  · push Not at h1
    have hpow : r ^ p.natDegree = -(∑ j ∈ Finset.range p.natDegree, p.coeff j * r ^ j) := by
      have heval : p.eval r = 0 := hr
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, one_mul] at heval
      linarith
    have habs : |r| ^ p.natDegree ≤ |r| ^ (p.natDegree - 1) * ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
      calc |r| ^ p.natDegree
          = |r ^ p.natDegree| := (abs_pow r p.natDegree).symm
        _ = |∑ j ∈ Finset.range p.natDegree, p.coeff j * r ^ j| := by rw [hpow, abs_neg]
        _ ≤ ∑ j ∈ Finset.range p.natDegree, |p.coeff j * r ^ j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j ∈ Finset.range p.natDegree, |p.coeff j| * |r| ^ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_pow]
        _ ≤ ∑ j ∈ Finset.range p.natDegree, |p.coeff j| * |r| ^ (p.natDegree - 1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' : j ≤ p.natDegree - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_of_lt h1) hj') (abs_nonneg _)
        _ = |r| ^ (p.natDegree - 1) * ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hd : 1 ≤ p.natDegree := by
      by_contra hd0
      push Not at hd0
      have h0 : p.natDegree = 0 := Nat.lt_one_iff.mp hd0
      have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
      rw [hp1] at hr
      simp at hr
    have hpos : 0 < |r| ^ (p.natDegree - 1) := pow_pos (by linarith) _
    have hmul : |r| ^ (p.natDegree - 1) * |r| ≤ |r| ^ (p.natDegree - 1) *
        ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
      rwa [← pow_succ, Nat.sub_add_cancel hd]
    have hle := le_of_mul_le_mul_left hmul hpos
    linarith

lemma sortedRoots_prod' {m : ℕ} {p : ℝ[X]} (hm : p.Monic) (hd : p.natDegree = m)
    (hr : RealRooted p) :
    p = ∏ i : Fin m, (X - C ((p.roots.sort (· ≥ ·)).getD i.val 0)) := by
  have hlen : (p.roots.sort (· ≥ ·)).length = m := by
    rw [Multiset.length_sort, hr.2, hd]
  have h1 := monic_eq_prod_roots_of_realRooted' hm hr
  have hcoe : (↑(p.roots.sort (· ≥ ·)) : Multiset ℝ) = p.roots := Multiset.sort_eq p.roots (· ≥ ·)
  conv_lhs => rw [h1, ← hcoe]
  rw [Multiset.map_coe, Multiset.prod_coe]
  have hlist_prod : ∀ (l : List ℝ[X]), l.length = m →
      l.prod = ∏ i : Fin m, l.getD i.val 1 := by
    intro l hl
    rw [← List.prod_ofFn (f := fun i : Fin m => l.getD i.val 1)]
    congr 1
    apply List.ext_getElem (by simp [hl])
    intro k hk1 _
    simp [List.getD, List.getElem?_eq_getElem hk1]
  rw [hlist_prod _ (by simp [hlen])]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : i.val < (p.roots.sort (· ≥ ·)).length := hlen ▸ i.isLt
  have hi' : i.val < ((p.roots.sort (· ≥ ·)).map (fun r => X - C r)).length := by simpa using hi
  simp [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']

lemma prod_linear_realRooted' {m : ℕ} (r : Fin m → ℝ) :
    RealRooted (∏ i : Fin m, (X - C (r i))) := by
  have hm : (∏ i : Fin m, (X - C (r i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  refine ⟨hm.ne_zero, ?_⟩
  rw [Polynomial.roots_prod _ _ hm.ne_zero]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.card_map]
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (r i))]
  simp

lemma tendsto_coeff_prod_linear' {m : ℕ} {r : ℕ → Fin m → ℝ} {r₀ : Fin m → ℝ}
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (nhds (r₀ i))) :
    ∀ j, Tendsto (fun n => (∏ i : Fin m, (X - C (r n i))).coeff j) atTop
      (nhds ((∏ i : Fin m, (X - C (r₀ i))).coeff j)) := by
  suffices ∀ s : Finset (Fin m), ∀ j,
      Tendsto (fun n => (∏ i ∈ s, (X - C (r n i))).coeff j) atTop
        (nhds ((∏ i ∈ s, (X - C (r₀ i))).coeff j)) from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro j
    simp only [Finset.prod_empty]
    exact tendsto_const_nhds
  | @insert a s ha ih =>
    intro j
    simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
    refine tendsto_finsetSum _ fun kl _ => ?_
    refine Tendsto.mul ?_ (ih kl.2)
    by_cases hk : kl.1 = 0
    · simp only [hk, Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub]
      exact (hr a).neg
    · by_cases hk1 : kl.1 = 1
      · simp only [hk1, Polynomial.coeff_sub, Polynomial.coeff_X_one,
          Polynomial.coeff_C_of_ne_zero one_ne_zero, sub_zero]
        exact tendsto_const_nhds
      · simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
          if_neg hk, if_neg (Ne.symm hk1), sub_zero]
        exact tendsto_const_nhds

lemma tendsto_realRooted {m : ℕ} {p : ℕ → ℝ[X]} {p₀ : ℝ[X]}
    (hpm : ∀ n, (p n).Monic) (hpd : ∀ n, (p n).natDegree = m)
    (hpr : ∀ n, RealRooted (p n))
    (htend : ∀ j, Tendsto (fun n => (p n).coeff j) atTop (nhds (p₀.coeff j))) :
    RealRooted p₀ := by
  let r : ℕ → Fin m → ℝ := fun n i => ((p n).roots.sort (· ≥ ·)).getD i.val 0
  have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n (i : Fin m), |r n i| ≤ M := by
    have hcbdd : ∀ j : Fin m, ∃ C : ℝ, ∀ n, |(p n).coeff j.val| ≤ C := by
      intro j
      obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (htend j.val)).subset_closedBall 0
      refine ⟨max C 0, fun n => ?_⟩
      have hmem : (p n).coeff j.val ∈ Metric.closedBall (0 : ℝ) C := hC ⟨n, rfl⟩
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
      exact le_trans hmem (le_max_left _ _)
    choose C hC using hcbdd
    refine ⟨1 + ∑ j : Fin m, max (C j) 0, ?_, fun n i => ?_⟩
    · have : 0 ≤ ∑ j : Fin m, max (C j) 0 := Finset.sum_nonneg fun j _ => le_max_right _ _
      linarith
    · have hlen : ((p n).roots.sort (· ≥ ·)).length = m := by
        rw [Multiset.length_sort, (hpr n).2, hpd n]
      have hi : i.val < ((p n).roots.sort (· ≥ ·)).length := hlen ▸ i.isLt
      have hmem : r n i ∈ (p n).roots := by
        have h1 : r n i ∈ (p n).roots.sort (· ≥ ·) := by
          simp only [r, List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem hi
        exact (Multiset.mem_sort (· ≥ ·)).mp h1
      have hroot : (p n).IsRoot (r n i) := (Polynomial.mem_roots (hpr n).1).mp hmem
      have hbound := abs_le_one_add_sum_coeff_of_isRoot' (hpm n) hroot
      rw [hpd n, ← Fin.sum_univ_eq_sum_range] at hbound
      calc |r n i| ≤ 1 + ∑ j : Fin m, |(p n).coeff j.val| := hbound
        _ ≤ 1 + ∑ j : Fin m, max (C j) 0 := by
          gcongr with j _
          exact le_trans (hC j n) (le_max_left _ _)
  obtain ⟨M, _, hM⟩ := hbdd
  let K : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-M) M)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hrK : ∀ n, r n ∈ K := fun n i _ => abs_le.mp (hM n i)
  obtain ⟨r₀, _, ψ, hψ, hlim⟩ := hK.tendsto_subseq hrK
  have hlim' : Tendsto (fun n => r (ψ n)) atTop (nhds r₀) := hlim
  have hp0_eq : p₀ = ∏ i : Fin m, (X - C (r₀ i)) := by
    ext j
    have h1 : Tendsto (fun n => (p (ψ n)).coeff j) atTop (nhds (p₀.coeff j)) :=
      (htend j).comp hψ.tendsto_atTop
    have h2 : Tendsto (fun n => (p (ψ n)).coeff j) atTop
        (nhds ((∏ i : Fin m, (X - C (r₀ i))).coeff j)) := by
      have heq : ∀ n, p (ψ n) = ∏ i : Fin m, (X - C (r (ψ n) i)) := fun n =>
        sortedRoots_prod' (hpm _) (hpd _) (hpr _)
      simpa only [heq] using tendsto_coeff_prod_linear' (tendsto_pi_nhds.mp hlim') j
    exact tendsto_nhds_unique h1 h2
  exact hp0_eq ▸ prod_linear_realRooted' r₀

lemma rescale_comp_monic_deg_realRooted {m : ℕ} {p : ℝ[X]} (hm : p.Monic) (hd : p.natDegree = m)
    (hr : RealRooted p) {t : ℝ} (ht : t ≠ 0) :
    let q := C (t⁻¹ ^ m) * p.comp (1 + C t * X)
    q.Monic ∧ q.natDegree = m ∧ RealRooted q := by
  let r : Fin m → ℝ := fun i => (p.roots.sort (· ≥ ·)).getD i.val 0
  have hp : p = ∏ i : Fin m, (X - C (r i)) := sortedRoots_prod' hm hd hr
  have hq_eq : C (t⁻¹ ^ m) * p.comp (1 + C t * X) =
      ∏ i : Fin m, (X - C ((r i - 1) / t)) := by
    rw [hp, Polynomial.prod_comp]
    have hterm : ∀ i : Fin m, (X - C (r i)).comp (1 + C t * X) =
        C t * (X - C ((r i - 1) / t)) := by
      intro i
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, mul_sub]
      have h1 : C t * C ((r i - 1) / t) = C (r i) - 1 := by
        rw [← C_mul, mul_div_cancel₀ _ ht, C_sub, C_1]
      rw [h1]
      ring
    simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← C_pow, ← mul_assoc, ← C_mul]
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero m ht), C_1, one_mul]
  dsimp only
  rw [hq_eq]
  refine ⟨Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _), ?_,
    prod_linear_realRooted' _⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
  simp

end RealRootedTools

/-! ### Section 2: All-ones matrix `onesMat`, `permMat`, and rank-one eigenspace shift -/

section OnesShift

def onesVec (m : ℕ) : Fin m → ℝ := fun _ => 1

def onesMat (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun _ _ => 1)

lemma onesMat_transpose (m : ℕ) : (onesMat m)ᵀ = onesMat m := by
  ext i j; rfl

lemma onesMat_isSymm (m : ℕ) : (onesMat m).IsSymm := onesMat_transpose m

lemma permMat_apply' {m : ℕ} (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    permMat σ i j = if j = σ i then 1 else 0 := by
  simp [permMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

lemma permMat_mul_eq {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permMat (σ * τ) = permMat τ * permMat σ := by
  ext i j
  simp only [permMat_apply', Matrix.mul_apply, Equiv.Perm.mul_apply]
  by_cases h : j = σ (τ i)
  · simp only [h, if_true]
    symm
    rw [Finset.sum_eq_single (τ i)]
    · simp
    · intro b _ hb; simp [hb]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · simp only [h, if_false]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = τ i
    · subst hb; simp [h]
    · simp [hb]

lemma conj_permMat_apply {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (σ : Equiv.Perm (Fin m))
    (i j : Fin m) :
    (permMat σ * B * (permMat σ)ᵀ) i j = B (σ i) (σ j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, permMat_apply']
  have h1 : ∀ k : Fin m, (∑ a : Fin m, (if a = σ i then (1 : ℝ) else 0) * B a k) = B (σ i) k := by
    intro k
    rw [Finset.sum_eq_single (σ i)]
    · simp
    · intro a _ ha; simp [ha]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  simp_rw [h1]
  rw [Finset.sum_eq_single (σ j)]
  · simp
  · intro k _ hk; simp [hk]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

lemma conj_permMat_onesMat {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    permMat σ * onesMat m * (permMat σ)ᵀ = onesMat m := by
  ext i j
  rw [conj_permMat_apply]
  rfl

lemma mul_onesMat_of_mulVec {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (h : M *ᵥ onesVec m = c • onesVec m) :
    M * onesMat m = c • onesMat m := by
  ext i j
  have hi := congr_fun h i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, onesVec, onesMat] using hi

lemma onesMat_mul_of_symm {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.IsSymm) {c : ℝ}
    (h : M * onesMat m = c • onesMat m) :
    onesMat m * M = c • onesMat m := by
  calc onesMat m * M = (Mᵀ * (onesMat m)ᵀ)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
    _ = (M * onesMat m)ᵀ := by rw [hM.eq, onesMat_transpose]
    _ = (c • onesMat m)ᵀ := by rw [h]
    _ = c • onesMat m := by rw [Matrix.transpose_smul, onesMat_transpose]

lemma onesMat_mul_onesMat (m : ℕ) :
    onesMat m * onesMat m = (m : ℝ) • onesMat m := by
  ext i j
  simp [onesMat, Matrix.mul_apply]

lemma charpoly_smul_onesMat (d : ℕ) (c : ℝ) :
    ((c / (d + 1 : ℝ)) • onesMat (d + 1)).charpoly = (X - C c) * X ^ d := by
  have hm_ne : (d + 1 : ℝ) ≠ 0 := by positivity
  let U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.of fun i j => if j = 0 then 1 else if i = 0 then -1 else if i = j then 1 else 0
  let V : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.of fun i k => if i = 0 then (d + 1 : ℝ)⁻¹ else (if i = k then 1 else 0) - (d + 1 : ℝ)⁻¹
  have hcol_sum : ∀ j : Fin (d + 1), j ≠ 0 → ∑ k : Fin (d + 1), U k j = 0 := by
    intro j hj
    rw [Fin.sum_univ_succ]
    have h0 : U 0 j = -1 := by simp [U, Matrix.of_apply, hj]
    have hrest : ∑ x : Fin d, U x.succ j = 1 := by
      obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj
      rw [Finset.sum_eq_single j']
      · simp [U, Matrix.of_apply]
      · intro b _ hb
        have hne : b.succ ≠ j'.succ := fun h => hb (Fin.succ_injective _ h)
        simp [U, Matrix.of_apply, hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    linarith
  have hVU : V * U = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj
        simp [U, V, Matrix.of_apply, hm_ne]
      · have hV0 : ∀ x : Fin (d + 1), V 0 x = (d + 1 : ℝ)⁻¹ := fun _ => by simp [V, Matrix.of_apply]
        simp_rw [hV0, ← Finset.mul_sum, hcol_sum j hj, mul_zero, if_neg (Ne.symm hj)]
    · by_cases hj : j = 0
      · subst hj
        have hU0 : ∀ x : Fin (d + 1), U x 0 = 1 := fun _ => by simp [U, Matrix.of_apply]
        have hVi : ∀ x : Fin (d + 1), V i x = (if i = x then (1 : ℝ) else 0) - (d + 1 : ℝ)⁻¹ :=
          fun _ => by simp [V, Matrix.of_apply, hi]
        simp_rw [hU0, mul_one, hVi, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin]
        have h1 : (∑ x : Fin (d + 1), if i = x then (1 : ℝ) else 0) = 1 := by simp
        rw [h1, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ hm_ne, sub_self, if_neg hi]
      · have hVi : ∀ x : Fin (d + 1), V i x = (if i = x then (1 : ℝ) else 0) - (d + 1 : ℝ)⁻¹ :=
          fun _ => by simp [V, Matrix.of_apply, hi]
        have hsub : ∑ x : Fin (d + 1), V i x * U x j =
            U i j - (d + 1 : ℝ)⁻¹ * ∑ x : Fin (d + 1), U x j := by
          simp_rw [hVi, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_eq_single i]
          · simp
          · intro b _ hb; simp [hb.symm]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [hsub, hcol_sum j hj, mul_zero, sub_zero]
        simp [U, Matrix.of_apply, hi, hj]
  have hUV : U * V = 1 := mul_eq_one_comm.mp hVU
  let D : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.diagonal fun j => if j = 0 then c else 0
  have hMU : ((c / (d + 1 : ℝ)) • onesMat (d + 1)) * U = U * D := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, onesMat, Matrix.of_apply, smul_eq_mul, mul_one,
      D, Matrix.diagonal_apply]
    by_cases hj : j = 0
    · subst hj
      have h1 : ∑ x : Fin (d + 1), c / (d + 1 : ℝ) * U x 0 = c := by
        simp only [U, Matrix.of_apply, if_true, mul_one, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
        field_simp [hm_ne]
      have h2 : ∑ x : Fin (d + 1), U i x * (if x = 0 then if x = 0 then c else 0 else 0) = c := by
        rw [Finset.sum_eq_single 0]
        · simp [U, Matrix.of_apply]
        · intro b _ hb; simp [hb]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      rw [h1, h2]
    · rw [← Finset.mul_sum, hcol_sum j hj, mul_zero]
      symm
      rw [Finset.sum_eq_single j]
      · simp [U, Matrix.of_apply, hj]
      · intro b _ hb
        by_cases hb0 : b = j
        · exact absurd hb0 hb
        · simp [hb0]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hsim : V * ((c / (d + 1 : ℝ)) • onesMat (d + 1)) * U = D := by
    rw [Matrix.mul_assoc, hMU, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  have hcp_eq : ((c / (d + 1 : ℝ)) • onesMat (d + 1)).charpoly = D.charpoly := by
    rw [← hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUV, Matrix.one_mul]
  rw [hcp_eq, Matrix.charpoly_diagonal, Fin.prod_univ_succ]
  simp

lemma charpoly_add_smul_onesMat (d : ℕ) (N : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hN : N * onesMat (d + 1) = 0) (c : ℝ) :
    X * (N + (c / (d + 1 : ℝ)) • onesMat (d + 1)).charpoly = (X - C c) * N.charpoly := by
  let P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := (c / (d + 1 : ℝ)) • onesMat (d + 1)
  have hNP : N * P = 0 := by
    simp [P, Matrix.mul_smul, hN]
  have hmat : Matrix.charmatrix N * Matrix.charmatrix P =
      Matrix.charmatrix (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) * Matrix.charmatrix (N + P) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.charmatrix, Matrix.mul_apply, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Matrix.add_apply, map_zero, sub_zero, map_add]
    have hNP_ij : ∑ k : Fin (d + 1), C (N i k) * C (P k j) = 0 := by
      have h0 : (N * P) i j = 0 := by rw [hNP]; rfl
      simp_rw [← map_mul, ← map_sum, Matrix.mul_apply] at *
      rw [h0, map_zero]
    have h1 : ∑ k : Fin (d + 1),
        ((if i = k then (X : ℝ[X]) else 0) - C (N i k)) *
          ((if k = j then (X : ℝ[X]) else 0) - C (P k j)) =
        (if i = j then X * X else 0) - X * C (P i j) - C (N i j) * X +
          ∑ k : Fin (d + 1), C (N i k) * C (P k j) := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      have s1 : (∑ k : Fin (d + 1), (if i = k then (X : ℝ[X]) else 0) * (if k = j then X else 0)) =
          if i = j then X * X else 0 := by
        rw [Finset.sum_eq_single i]
        · by_cases hij : i = j <;> simp [hij]
        · intro k _ hk; simp [hk.symm]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      have s2 : (∑ k : Fin (d + 1), (if i = k then (X : ℝ[X]) else 0) * C (P k j)) = X * C (P i j) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hk; simp [hk.symm]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      have s3 : (∑ k : Fin (d + 1), C (N i k) * (if k = j then (X : ℝ[X]) else 0)) = C (N i j) * X := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [hk]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      rw [s1, s2, s3]
      ring
    have h2 : ∑ k : Fin (d + 1),
        (if i = k then (X : ℝ[X]) else 0) *
          ((if k = j then (X : ℝ[X]) else 0) - (C (N k j) + C (P k j))) =
        (if i = j then X * X else 0) - X * C (N i j) - X * C (P i j) := by
      rw [Finset.sum_eq_single i]
      · by_cases hij : i = j <;> simp [hij] <;> ring
      · intro k _ hk; simp [hk.symm]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    rw [h1, hNP_ij, add_zero, h2]
    ring
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  change N.charpoly * P.charpoly =
    (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).charpoly * (N + P).charpoly at hdet
  have h0cp : (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).charpoly = X ^ (d + 1) := by
    simp [Matrix.charpoly_zero]
  rw [charpoly_smul_onesMat d c, h0cp, pow_succ'] at hdet
  have hcancel : X ^ d * (X * (N + P).charpoly) = X ^ d * ((X - C c) * N.charpoly) := by
    calc X ^ d * (X * (N + P).charpoly)
        = (X * X ^ d) * (N + P).charpoly := by ring
      _ = N.charpoly * ((X - C c) * X ^ d) := hdet.symm
      _ = X ^ d * ((X - C c) * N.charpoly) := by ring
  exact mul_left_cancel₀ (pow_ne_zero d Polynomial.X_ne_zero) hcancel

lemma permAvg_mul_left {m : ℕ} (P : ℝ[X]) (F : Equiv.Perm (Fin m) → ℝ[X]) :
    P * permAvg F = permAvg (fun σ => P * F σ) := by
  simp only [permAvg, mul_smul_comm, Finset.mul_sum]

end OnesShift

/-! ### Section 3: Ordered-tuple Cauchy–Binet and permutation average of principal minors -/

section MinorsQuadrature

noncomputable def sumMinors {m : ℕ} (k : ℕ) (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    (M.submatrix (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det

noncomputable def tupleMinorSum {m : ℕ} (k : ℕ) (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ e : Fin k → Fin m, (M.submatrix e e).det

lemma det_submatrix_eq_zero_of_not_injective_row {k m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    {f : Fin k → Fin m} (hf : ¬Function.Injective f) (g : Fin k → Fin n) :
    (M.submatrix f g).det = 0 := by
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨i, j, hij_eq, hij_ne⟩ := hf
  exact Matrix.det_zero_of_row_eq hij_ne (by ext c; simp [hij_eq])

lemma det_submatrix_eq_zero_of_not_injective_col {k m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (f : Fin k → Fin m) {g : Fin k → Fin n} (hg : ¬Function.Injective g) :
    (M.submatrix f g).det = 0 := by
  simp only [Function.Injective, not_forall] at hg
  obtain ⟨i, j, hij_eq, hij_ne⟩ := hg
  exact Matrix.det_zero_of_column_eq hij_ne (fun r => by simp [hij_eq])

lemma tupleMinorSum_eq_factorial_mul_sumMinors {m : ℕ} (k : ℕ) (M : Matrix (Fin m) (Fin m) ℝ) :
    tupleMinorSum k M = (k.factorial : ℝ) * sumMinors k M := by
  classical
  unfold tupleMinorSum sumMinors
  let injSet : Finset (Fin k → Fin m) := Finset.univ.filter Function.Injective
  have hrestrict : (∑ e : Fin k → Fin m, (M.submatrix e e).det) =
      ∑ e ∈ injSet, (M.submatrix e e).det := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun e _ he => ?_
    have hni : ¬Function.Injective e := by simpa [injSet] using he
    exact det_submatrix_eq_zero_of_not_injective_row M hni e
  rw [hrestrict]
  have hmaps : ∀ e ∈ injSet, Finset.univ.image e ∈ (Finset.univ : Finset (Fin m)).powersetCard k := by
    intro e he
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp he).2, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
  let es : Fin k ≃ s := (s.orderIsoOfFin hscard).toEquiv
  let φ : Equiv.Perm (Fin k) → (Fin k → Fin m) := fun π i => (es (π i)).val
  have hbij : Finset.image φ Finset.univ = injSet.filter (fun e => Finset.univ.image e = s) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, injSet]
    constructor
    · rintro ⟨π, rfl⟩
      refine ⟨Subtype.val_injective.comp (es.injective.comp π.injective), ?_⟩
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, φ]
      constructor
      · rintro ⟨i, rfl⟩; exact (es (π i)).prop
      · intro hx; exact ⟨π⁻¹ (es.symm ⟨x, hx⟩), by simp⟩
    · rintro ⟨he_inj, he_img⟩
      let eSub : Fin k → s := fun i => ⟨e i, he_img ▸ Finset.mem_image_of_mem e (Finset.mem_univ i)⟩
      have heSub_inj : Function.Injective eSub := fun i j h => he_inj (congrArg Subtype.val h)
      have hcard_eq : Fintype.card (Fin k) = Fintype.card s := by simp [hscard]
      have heSub_bij : Function.Bijective eSub :=
        (Fintype.bijective_iff_injective_and_card eSub).mpr ⟨heSub_inj, hcard_eq⟩
      refine ⟨(Equiv.ofBijective eSub heSub_bij).trans es.symm, ?_⟩
      funext i
      simp [φ, eSub]
  have hφ_inj : Function.Injective φ := by
    intro π₁ π₂ h
    refine Equiv.ext fun i => ?_
    have hi := congr_fun h i
    exact es.injective (Subtype.ext hi)
  rw [← hbij, Finset.sum_image (fun π₁ _ π₂ _ h => hφ_inj h)]
  have hterm : ∀ π : Equiv.Perm (Fin k),
      (M.submatrix (φ π) (φ π)).det =
        (M.submatrix (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det := by
    intro π
    have hsub : M.submatrix (φ π) (φ π) =
        (M.submatrix (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).submatrix
          (π.trans es) (π.trans es) := rfl
    rw [hsub, Matrix.det_submatrix_equiv_self]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

lemma cauchy_binet_tuples {k m : ℕ} (M : Matrix (Fin k) (Fin m) ℝ) (N : Matrix (Fin m) (Fin k) ℝ) :
    (∑ f : Fin k → Fin m, (M.submatrix id f).det * (N.submatrix f id).det) =
      (k.factorial : ℝ) * (M * N).det := by
  have hNdet : ∀ f : Fin k → Fin m,
      (N.submatrix f id).det =
        ∑ π : Equiv.Perm (Fin k), (Equiv.Perm.sign π : ℝ) * ∏ j : Fin k, N (f (π j)) j := by
    intro f
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun π _ => ?_
    simp
  simp_rw [hNdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hπ_const : ∀ π : Equiv.Perm (Fin k),
      (∑ f : Fin k → Fin m, (M.submatrix id f).det *
        ((Equiv.Perm.sign π : ℝ) * ∏ j : Fin k, N (f (π j)) j)) =
      ∑ g : Fin k → Fin m, (M.submatrix id g).det * ∏ j : Fin k, N (g j) j := by
    intro π
    let eqv : (Fin k → Fin m) ≃ (Fin k → Fin m) :=
      { toFun := fun g i => g (π⁻¹ i)
        invFun := fun f i => f (π i)
        left_inv := fun g => funext fun i => by simp
        right_inv := fun f => funext fun i => by simp }
    rw [← Equiv.sum_comp eqv]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hsub : M.submatrix id (eqv g) = (M.submatrix id g).submatrix id (π⁻¹ : Equiv.Perm (Fin k)) := rfl
    have hdet : (M.submatrix id (eqv g)).det =
        (Equiv.Perm.sign (π⁻¹ : Equiv.Perm (Fin k)) : ℝ) * (M.submatrix id g).det := by
      rw [hsub, Matrix.det_permute']
    have hprod : (∏ j : Fin k, N (eqv g (π j)) j) = ∏ j : Fin k, N (g j) j := by
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [eqv]
    have hsign : (Equiv.Perm.sign (π⁻¹ : Equiv.Perm (Fin k)) : ℝ) * (Equiv.Perm.sign π : ℝ) = 1 := by
      rw [Equiv.Perm.sign_inv]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
    rw [hdet, hprod]
    calc ((Equiv.Perm.sign (π⁻¹ : Equiv.Perm (Fin k)) : ℝ) * (M.submatrix id g).det) *
          ((Equiv.Perm.sign π : ℝ) * ∏ j : Fin k, N (g j) j)
        = ((Equiv.Perm.sign (π⁻¹ : Equiv.Perm (Fin k)) : ℝ) * (Equiv.Perm.sign π : ℝ)) *
          ((M.submatrix id g).det * ∏ j : Fin k, N (g j) j) := by ring
      _ = (M.submatrix id g).det * ∏ j : Fin k, N (g j) j := by rw [hsign, one_mul]
  simp_rw [hπ_const]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  have hMdet : ∀ g : Fin k → Fin m,
      (M.submatrix id g).det * (∏ j : Fin k, N (g j) j) =
        ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℝ) *
          ∏ j : Fin k, (M (τ j) (g j) * N (g j) j) := by
    intro g
    rw [Matrix.det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [hMdet]
  rw [Finset.sum_comm, Matrix.det_apply']
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Matrix.mul_apply]
  exact (Fintype.prod_sum (fun j p => M (τ j) p * N p j)).symm

lemma exists_perm_comp_eq {m : ℕ} : ∀ {k : ℕ} {e g : Fin k → Fin m},
    Function.Injective e → Function.Injective g →
    ∃ τ : Equiv.Perm (Fin m), τ ∘ e = g
  | 0, e, g, _, _ => ⟨1, funext fun i => Fin.elim0 i⟩
  | k + 1, e, g, he, hg => by
    obtain ⟨τ₀, hτ₀⟩ := exists_perm_comp_eq (k := k)
      (he.comp (Fin.castSucc_injective k)) (hg.comp (Fin.castSucc_injective k))
    let τ : Equiv.Perm (Fin m) := Equiv.swap (τ₀ (e (Fin.last k))) (g (Fin.last k)) * τ₀
    refine ⟨τ, funext fun i => ?_⟩
    refine Fin.lastCases ?_ ?_ i
    · simp [τ]
    · intro j
      have hj : τ₀ (e j.castSucc) = g j.castSucc := congr_fun hτ₀ j
      have hne1 : g j.castSucc ≠ τ₀ (e (Fin.last k)) := by
        intro h
        have h1 : τ₀ (e j.castSucc) = τ₀ (e (Fin.last k)) := hj.trans h
        exact Fin.castSucc_ne_last j (he (τ₀.injective h1))
      have hne2 : g j.castSucc ≠ g (Fin.last k) := fun h =>
        Fin.castSucc_ne_last j (hg h)
      simp only [Function.comp_apply, τ, Equiv.Perm.mul_apply, hj]
      exact Equiv.swap_apply_of_ne_of_ne hne1 hne2

lemma det_updateRow_finset_sum {k : ℕ} {ι : Type*} (M : Matrix (Fin k) (Fin k) ℝ)
    (r : Fin k) (S : Finset ι) (u : ι → Fin k → ℝ) :
    (M.updateRow r (∑ v ∈ S, u v)).det = ∑ v ∈ S, (M.updateRow r (u v)).det := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero r (fun j => by simp)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Matrix.det_updateRow_add, Finset.sum_insert ha, ih]

lemma det_updateCol_finset_sum {k : ℕ} {ι : Type*} (M : Matrix (Fin k) (Fin k) ℝ)
    (r : Fin k) (S : Finset ι) (u : ι → Fin k → ℝ) :
    (M.updateCol r (∑ v ∈ S, u v)).det = ∑ v ∈ S, (M.updateCol r (u v)).det := by
  rw [← Matrix.det_transpose, ← Matrix.updateRow_transpose, det_updateRow_finset_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.updateRow_transpose, Matrix.det_transpose]

/-- Average minor identity for `A₀ P_σ B₀ P_σᵀ` when `A₀` and `B₀` have row and column sums `0`. -/
lemma avg_sumMinors_mul_zero_sum (d : ℕ) (A₀ B₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hA₀_row : A₀ * onesMat (d + 1) = 0)
    (hB₀_col : onesMat (d + 1) * B₀ = 0)
    (k : ℕ) (hk : k ≤ d) :
    ((Fintype.card (Equiv.Perm (Fin (d + 1))) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (d + 1)),
        sumMinors k (A₀ * permMat σ * B₀ * (permMat σ)ᵀ)) =
      sumMinors k A₀ * sumMinors k B₀ / (d.choose k : ℝ) := by
  classical
  let m := d + 1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hmk_pos : 1 ≤ m - k := by omega
  have hmk_ne : ((m - k : ℕ) : ℝ) ≠ 0 := by positivity
  have hkfac_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hperm_ne : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  let Cmat : Equiv.Perm (Fin m) → Matrix (Fin m) (Fin m) ℝ :=
    fun σ => permMat σ * B₀ * (permMat σ)ᵀ
  have hprod_assoc : ∀ σ, A₀ * permMat σ * B₀ * (permMat σ)ᵀ = A₀ * Cmat σ := fun σ => by
    simp [Cmat, Matrix.mul_assoc]
  simp_rw [hprod_assoc]
  -- Define `Mavg f e := E_σ [det((Cmat σ).submatrix f e)]`
  let Mavg : (Fin k → Fin m) → (Fin k → Fin m) → ℝ := fun f e =>
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin m), ((Cmat σ).submatrix f e).det
  -- Equivariance of `Mavg`: `Mavg (τ ∘ f) (τ ∘ e) = Mavg f e`
  have hMavg_equiv : ∀ (τ : Equiv.Perm (Fin m)) (f e : Fin k → Fin m),
      Mavg (τ ∘ f) (τ ∘ e) = Mavg f e := by
    intro τ f e
    simp only [Mavg]
    congr 1
    let eqv : Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) :=
      { toFun := fun σ => σ * τ
        invFun := fun σ => σ * τ⁻¹
        left_inv := fun σ => by simp
        right_inv := fun σ => by simp }
    refine Fintype.sum_equiv eqv _ _ fun σ => ?_
    apply congrArg Matrix.det
    ext i j
    simp [Cmat, conj_permMat_apply, eqv]
  -- Row permutation of `Mavg`: `Mavg (f ∘ π) e = sign(π) * Mavg f e`
  have hMavg_perm_left : ∀ (f e : Fin k → Fin m) (π : Equiv.Perm (Fin k)),
      Mavg (f ∘ π) e = (Equiv.Perm.sign π : ℝ) * Mavg f e := by
    intro f e π
    simp only [Mavg]
    rw [← mul_assoc, mul_comm (Equiv.Perm.sign π : ℝ), mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hsub : (Cmat σ).submatrix (f ∘ π) e = ((Cmat σ).submatrix f e).submatrix π id := rfl
    rw [hsub, Matrix.det_permute]
  -- Diagonal constancy and exact value of `Mavg e e` for injective `e`
  have hMavg_diag : ∀ {e : Fin k → Fin m}, Function.Injective e →
      Mavg e e = sumMinors k B₀ / (m.choose k : ℝ) := by
    intro e he
    have hconst : ∀ {g : Fin k → Fin m}, Function.Injective g → Mavg g g = Mavg e e := by
      intro g hg
      obtain ⟨τ, hτ⟩ := exists_perm_comp_eq he hg
      rw [← hτ, hMavg_equiv]
    let injSet : Finset (Fin k → Fin m) := Finset.univ.filter Function.Injective
    have hsum_inj : ∑ g ∈ injSet, Mavg g g = (k.factorial : ℝ) * sumMinors k B₀ := by
      have h1 : ∑ g ∈ injSet, Mavg g g =
          (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin m), tupleMinorSum k (Cmat σ) := by
        simp only [Mavg, tupleMinorSum, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        refine Finset.sum_subset (Finset.filter_subset _ _) fun g _ hg => ?_
        have hni : ¬Function.Injective g := by
          simp only [injSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg
          exact hg
        exact det_submatrix_eq_zero_of_not_injective_row (Cmat σ) hni g
      have hC_minors : ∀ σ, tupleMinorSum k (Cmat σ) = (k.factorial : ℝ) * sumMinors k B₀ := by
        intro σ
        have h2 : tupleMinorSum k (Cmat σ) = tupleMinorSum k B₀ := by
          unfold tupleMinorSum
          let eqv : (Fin k → Fin m) ≃ (Fin k → Fin m) :=
            { toFun := fun g i => σ (g i)
              invFun := fun g i => σ⁻¹ (g i)
              left_inv := fun g => funext fun i => by simp
              right_inv := fun g => funext fun i => by simp }
          refine Fintype.sum_equiv eqv _ _ fun g => ?_
          congr 1; ext i j; simp [Cmat, conj_permMat_apply, eqv]
        rw [h2, tupleMinorSum_eq_factorial_mul_sumMinors]
      rw [h1]
      simp_rw [hC_minors]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hperm_ne, one_mul]
    have hcard_inj : (injSet.card : ℝ) = (k.factorial : ℝ) * (m.choose k : ℝ) := by
      have hone := tupleMinorSum_eq_factorial_mul_sumMinors k (1 : Matrix (Fin m) (Fin m) ℝ)
      have h1 : tupleMinorSum k (1 : Matrix (Fin m) (Fin m) ℝ) = (injSet.card : ℝ) := by
        unfold tupleMinorSum
        have hsub : (∑ g : Fin k → Fin m, ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix g g).det) =
            ∑ g ∈ injSet, ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix g g).det := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun g _ hg => ?_
          have hni : ¬Function.Injective g := by
            simp only [injSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg
            exact hg
          exact det_submatrix_eq_zero_of_not_injective_row _ hni g
        rw [hsub]
        have hdet1 : ∀ g ∈ injSet, ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix g g).det = 1 := by
          intro g hg
          have hinj := (Finset.mem_filter.mp hg).2
          have hmat : (1 : Matrix (Fin m) (Fin m) ℝ).submatrix g g = 1 := by
            ext i j
            simp [Matrix.one_apply, hinj.eq_iff]
          rw [hmat, Matrix.det_one]
        rw [Finset.sum_congr rfl hdet1, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h2 : sumMinors k (1 : Matrix (Fin m) (Fin m) ℝ) = (m.choose k : ℝ) := by
        unfold sumMinors
        have hdet1 : ∀ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix
              (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det = 1 := by
          intro s _
          have hmat : (1 : Matrix (Fin m) (Fin m) ℝ).submatrix
              (Subtype.val : s → Fin m) (Subtype.val : s → Fin m) = 1 := by
            ext i j
            by_cases hij : i = j
            · subst hij; simp
            · have hne : (i : Fin m) ≠ (j : Fin m) := fun h => hij (Subtype.ext h)
              simp [Matrix.one_apply, hij, hne]
          rw [hmat, Matrix.det_one]
        rw [Finset.sum_congr rfl hdet1, Finset.sum_const, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [← h1, hone, h2]
    have hsum_const : ∑ g ∈ injSet, Mavg g g = (injSet.card : ℝ) * Mavg e e := by
      rw [Finset.sum_congr rfl (fun g hg => hconst (Finset.mem_filter.mp hg).2),
        Finset.sum_const, nsmul_eq_mul]
    have hmchoose_ne : (m.choose k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [hsum_const, hcard_inj] at hsum_inj
    have hcancel := mul_left_cancel₀ hkfac_ne (by linarith :
      (k.factorial : ℝ) * ((m.choose k : ℝ) * Mavg e e) = (k.factorial : ℝ) * sumMinors k B₀)
    exact (eq_div_iff hmchoose_ne).mpr (by linarith)
  -- Off-diagonal single-replacement value `Mavg (Function.update e r v) e` for `v ∉ range e`
  have hMavg_shift : ∀ {e : Fin k → Fin m} (he : Function.Injective e) (r : Fin k)
      {v : Fin m} (hv : v ∉ Finset.univ.image e),
      Mavg (Function.update e r v) e = -Mavg e e / ((m - k : ℕ) : ℝ) := by
    intro e he r v hv
    let S : Finset (Fin m) := Finset.univ.image e
    have hScard : S.card = k := by
      rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]
    have hcompl_card : (Sᶜ.card : ℝ) = ((m - k : ℕ) : ℝ) := by
      rw [Finset.card_compl, Fintype.card_fin, hScard]
    -- Column sum of `Cmat σ` is `0` because `onesMat m * B₀ = 0`
    have hC_col_sum : ∀ (σ : Equiv.Perm (Fin m)) (j : Fin m), ∑ w : Fin m, Cmat σ w j = 0 := by
      intro σ j
      have h1 : onesMat m * Cmat σ = 0 := by
        calc onesMat m * (permMat σ * B₀ * (permMat σ)ᵀ)
            = (permMat σ * onesMat m * (permMat σ)ᵀ) * (permMat σ * B₀ * (permMat σ)ᵀ) := by
                rw [conj_permMat_onesMat]
          _ = permMat σ * (onesMat m * ((permMat σ)ᵀ * permMat σ) * B₀) * (permMat σ)ᵀ := by
                simp only [Matrix.mul_assoc]
          _ = 0 := by
                have htp : (permMat σ)ᵀ * permMat σ = 1 := by
                  have htr : (permMat σ)ᵀ = permMat σ⁻¹ := by
                    ext a b; simp [permMat_apply', eq_comm, σ.eq_symm_apply]
                  rw [htr, ← permMat_mul_eq, mul_inv_cancel, show permMat (1 : Equiv.Perm (Fin m)) = 1 by
                    ext a b; simp [permMat_apply', Matrix.one_apply, eq_comm]]
                rw [htp, Matrix.mul_one, hB₀_col, Matrix.mul_zero, Matrix.zero_mul]
      have h0 : (onesMat m * Cmat σ) 0 j = 0 := by rw [h1]; rfl
      simpa [Matrix.mul_apply, onesMat] using h0
    -- Sum of `Mavg (update e r w) e` over ALL `w : Fin m` is `0`
    have hsum_all : ∑ w : Fin m, Mavg (Function.update e r w) e = 0 := by
      simp only [Mavg, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      have hσ0 : ∀ σ : Equiv.Perm (Fin m),
          ∑ w : Fin m, ((Cmat σ).submatrix (Function.update e r w) e).det = 0 := by
        intro σ
        have hupd : ∀ w : Fin m,
            (Cmat σ).submatrix (Function.update e r w) e =
              ((Cmat σ).submatrix e e).updateRow r (fun j => Cmat σ w (e j)) := by
          intro w; ext i j
          by_cases hir : i = r <;> simp [hir]
        simp_rw [hupd, ← det_updateRow_finset_sum]
        have hrow0 : (∑ w ∈ (Finset.univ : Finset (Fin m)), fun j : Fin k => Cmat σ w (e j)) = 0 := by
          funext j
          simp [Finset.sum_apply, hC_col_sum σ (e j)]
        rw [hrow0]
        exact Matrix.det_eq_zero_of_row_eq_zero r (fun _ => by simp)
      simp_rw [hσ0, Finset.sum_const_zero, mul_zero]
    -- Split `Finset.univ` into `S` and `Sᶜ`
    have hsum_S : ∑ w ∈ S, Mavg (Function.update e r w) e = Mavg e e := by
      rw [Finset.sum_eq_single (e r)]
      · rw [Function.update_eq_self]
      · intro w hw hne
        obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hw
        have hr' : r' ≠ r := fun h => hne (congrArg e h)
        have hni : ¬Function.Injective (Function.update e r (e r')) := by
          intro hinj
          have heq : Function.update e r (e r') r = Function.update e r (e r') r' := by
            rw [Function.update_self, Function.update_of_ne hr']
          exact hr' (hinj heq).symm
        have h0 : ∀ σ, ((Cmat σ).submatrix (Function.update e r (e r')) e).det = 0 :=
          fun σ => det_submatrix_eq_zero_of_not_injective_row _ hni e
        dsimp only [Mavg]
        simp [h0]
      · intro hmem; exact absurd (Finset.mem_image_of_mem e (Finset.mem_univ r)) hmem
    have hconst_compl : ∀ w ∈ Sᶜ,
        Mavg (Function.update e r w) e = Mavg (Function.update e r v) e := by
      intro w hw
      have hw' : w ∉ S := Finset.mem_compl.mp hw
      let τ : Equiv.Perm (Fin m) := Equiv.swap v w
      have hτe : τ ∘ e = e := by
        funext j
        have hej : e j ∈ S := Finset.mem_image_of_mem e (Finset.mem_univ j)
        have h1 : e j ≠ v := fun h => hv (by rwa [← h])
        have h2 : e j ≠ w := fun h => hw' (by rwa [← h])
        exact Equiv.swap_apply_of_ne_of_ne h1 h2
      have hτupd : τ ∘ Function.update e r v = Function.update e r w := by
        funext j
        by_cases hjr : j = r
        · subst hjr; simp [τ]
        · simp only [Function.comp_apply, Function.update_of_ne hjr]
          exact congr_fun hτe j
      calc Mavg (Function.update e r w) e
          = Mavg (τ ∘ Function.update e r v) (τ ∘ e) := by rw [hτupd, hτe]
        _ = Mavg (Function.update e r v) e := hMavg_equiv τ _ _
    have hsplit : (∑ w : Fin m, Mavg (Function.update e r w) e) =
        (∑ w ∈ S, Mavg (Function.update e r w) e) +
        (∑ w ∈ Sᶜ, Mavg (Function.update e r w) e) := by
      rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
    rw [hsum_S, Finset.sum_congr rfl hconst_compl, Finset.sum_const, nsmul_eq_mul,
      hcompl_card] at hsplit
    rw [hsplit] at hsum_all
    exact (eq_div_iff hmk_ne).mpr (by linarith)
  -- Vanishing of `Mavg f e` when `f` is non-injective or misses `≥ 2` elements outside `im e`
  have hMavg_zero_ge2 : ∀ {f e : Fin k → Fin m} (hf : Function.Injective f)
      {i₁ i₂ : Fin k} (hne : i₁ ≠ i₂)
      (h1 : f i₁ ∉ Finset.univ.image e) (h2 : f i₂ ∉ Finset.univ.image e),
      Mavg f e = 0 := by
    intro f e hf i₁ i₂ hne h1 h2
    let τ : Equiv.Perm (Fin m) := Equiv.swap (f i₁) (f i₂)
    have hτe : τ ∘ e = e := by
      funext j
      have hej : e j ∈ Finset.univ.image e := Finset.mem_image_of_mem e (Finset.mem_univ j)
      exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rwa [← h])) (fun h => h2 (by rwa [← h]))
    have hτf : τ ∘ f = f ∘ Equiv.swap i₁ i₂ := by
      funext i
      by_cases hi1 : i = i₁
      · subst hi1; simp [τ]
      · by_cases hi2 : i = i₂
        · subst hi2; simp [τ]
        · simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hi1 hi2]
          exact Equiv.swap_apply_of_ne_of_ne (fun h => hi1 (hf h)) (fun h => hi2 (hf h))
    have heq1 : Mavg f e = Mavg (τ ∘ f) (τ ∘ e) := (hMavg_equiv τ f e).symm
    rw [hτf, hτe, hMavg_perm_left, Equiv.Perm.sign_swap hne] at heq1
    norm_num at heq1
    linarith
  -- Evaluate `∑ f, det(A₀.submatrix e f) * Mavg f e` for fixed injective `e`
  have dinner_sum : ∀ {e : Fin k → Fin m}, Function.Injective e →
      (∑ f : Fin k → Fin m, (A₀.submatrix e f).det * Mavg f e) =
        (k.factorial : ℝ) * (A₀.submatrix e e).det * (sumMinors k B₀ / (d.choose k : ℝ)) := by
    intro e he
    let S : Finset (Fin m) := Finset.univ.image e
    let outCard : (Fin k → Fin m) → ℕ := fun f =>
      (Finset.univ.filter (fun i : Fin k => f i ∉ S)).card
    let F0 : Finset (Fin k → Fin m) :=
      Finset.univ.filter (fun f => Function.Injective f ∧ outCard f = 0)
    let F1 : Finset (Fin k → Fin m) :=
      Finset.univ.filter (fun f => Function.Injective f ∧ outCard f = 1)
    have hdisj : Disjoint F0 F1 := by
      rw [Finset.disjoint_filter]
      intro f _ h0 h1; omega
    have hred : (∑ f : Fin k → Fin m, (A₀.submatrix e f).det * Mavg f e) =
        (∑ f ∈ F0, (A₀.submatrix e f).det * Mavg f e) +
        (∑ f ∈ F1, (A₀.submatrix e f).det * Mavg f e) := by
      rw [← Finset.sum_union hdisj]
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun f _ hf => ?_
      by_cases hfinj : Function.Injective f
      · have hnot0 : outCard f ≠ 0 := fun h0 =>
          hf (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hfinj, h0⟩))
        have hnot1 : outCard f ≠ 1 := fun h1 =>
          hf (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hfinj, h1⟩))
        obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < outCard f)
        have hm0 := hMavg_zero_ge2 hfinj hne (Finset.mem_filter.mp hi₁).2
          (Finset.mem_filter.mp hi₂).2
        rw [hm0, mul_zero]
      · rw [det_submatrix_eq_zero_of_not_injective_col A₀ e hfinj, zero_mul]
    -- Sum over `F0`: `f = e ∘ π` for `π : Perm (Fin k)`
    have hF0 : (∑ f ∈ F0, (A₀.submatrix e f).det * Mavg f e) =
        (k.factorial : ℝ) * (A₀.submatrix e e).det * Mavg e e := by
      let φ0 : Equiv.Perm (Fin k) → (Fin k → Fin m) := fun π => e ∘ π
      have hφ0_inj : Function.Injective φ0 := fun π₁ π₂ h =>
        Equiv.ext fun i => he (congr_fun h i)
      have hφ0_img : Finset.image φ0 Finset.univ = F0 := by
        ext f
        simp only [Finset.mem_image, Finset.mem_univ, true_and, F0, Finset.mem_filter]
        constructor
        · rintro ⟨π, rfl⟩
          refine ⟨he.comp π.injective, ?_⟩
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro i _
          exact not_not.mpr (Finset.mem_image_of_mem e (Finset.mem_univ (π i)))
        · rintro ⟨hfinj, hcard0⟩
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard0
          have hg : ∀ i : Fin k, ∃ j : Fin k, e j = f i := fun i => by
            have hmemS : f i ∈ S := by
              by_contra hns
              exact hcard0 (Finset.mem_univ i) hns
            obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmemS
            exact ⟨j, hj⟩
          choose p hp using hg
          have hp_inj : Function.Injective p := fun i₁ i₂ h =>
            hfinj ((hp i₁).symm.trans ((congrArg e h).trans (hp i₂)))
          have hp_bij : Function.Bijective p := Finite.injective_iff_bijective.mp hp_inj
          exact ⟨Equiv.ofBijective p hp_bij, funext hp⟩
      rw [← hφ0_img, Finset.sum_image (fun _ _ _ _ h => hφ0_inj h)]
      have hterm0 : ∀ π : Equiv.Perm (Fin k),
          (A₀.submatrix e (φ0 π)).det * Mavg (φ0 π) e = (A₀.submatrix e e).det * Mavg e e := by
        intro π
        have hdet : (A₀.submatrix e (e ∘ π)).det =
            (Equiv.Perm.sign π : ℝ) * (A₀.submatrix e e).det := by
          have hsub : A₀.submatrix e (e ∘ π) = (A₀.submatrix e e).submatrix id π := rfl
          rw [hsub, Matrix.det_permute']
        dsimp only [φ0]
        rw [hdet, hMavg_perm_left]
        have hsign : (Equiv.Perm.sign π : ℝ) * (Equiv.Perm.sign π : ℝ) = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
        calc ((Equiv.Perm.sign π : ℝ) * (A₀.submatrix e e).det) *
              ((Equiv.Perm.sign π : ℝ) * Mavg e e)
            = ((Equiv.Perm.sign π : ℝ) * (Equiv.Perm.sign π : ℝ)) *
              ((A₀.submatrix e e).det * Mavg e e) := by ring
          _ = (A₀.submatrix e e).det * Mavg e e := by rw [hsign, one_mul]
      simp_rw [hterm0]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      ring
    -- Sum over `F1`: `f = (Function.update e r v) ∘ π` for `(r, v, π) ∈ Fin k ×ˢ Sᶜ ×ˢ univ`
    have hF1 : (∑ f ∈ F1, (A₀.submatrix e f).det * Mavg f e) =
        (k.factorial : ℝ) * ((k : ℝ) / ((m - k : ℕ) : ℝ)) * (A₀.submatrix e e).det * Mavg e e := by
      let dom : Finset (Fin k × Fin m × Equiv.Perm (Fin k)) :=
        Finset.univ ×ˢ (Sᶜ ×ˢ Finset.univ)
      let φ1 : Fin k × Fin m × Equiv.Perm (Fin k) → (Fin k → Fin m) :=
        fun ⟨r, v, π⟩ => Function.update e r v ∘ π
      have hφ1_inj : ∀ x ∈ dom, ∀ y ∈ dom, φ1 x = φ1 y → x = y := by
        rintro ⟨r₁, v₁, π₁⟩ hx ⟨r₂, v₂, π₂⟩ hy h
        have hv1 : v₁ ∉ S := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
        have hv2 : v₂ ∉ S := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_product.mp hy).2).1
        have hout1 : φ1 (r₁, v₁, π₁) (π₁⁻¹ r₁) = v₁ := by simp [φ1]
        have hin2 : ∀ j : Fin k, π₂ j ≠ r₂ → φ1 (r₂, v₂, π₂) j ∈ S := by
          intro j hj
          simp only [φ1, Function.comp_apply, Function.update_of_ne hj]
          exact Finset.mem_image_of_mem e (Finset.mem_univ _)
        have hπ_eq : π₂ (π₁⁻¹ r₁) = r₂ := by
          by_contra hne
          have hmem := hin2 (π₁⁻¹ r₁) hne
          rw [← h, hout1] at hmem
          exact hv1 hmem
        have hv_eq : v₁ = v₂ := by
          have hval0 := congr_fun h (π₁⁻¹ r₁)
          rw [hout1] at hval0
          simp only [φ1, Function.comp_apply, hπ_eq, Function.update_self] at hval0
          exact hval0
        subst hv_eq
        have hr_eq : r₁ = r₂ := by
          by_contra hr_ne
          have hr_ne' : r₂ ≠ r₁ := fun heq => hr_ne heq.symm
          have hval : φ1 (r₁, v₁, π₁) (π₁⁻¹ r₂) = e r₂ := by
            simp [φ1, hr_ne']
          rw [h] at hval
          by_cases hq : π₂ (π₁⁻¹ r₂) = r₂
          · simp only [φ1, Function.comp_apply, hq, Function.update_self] at hval
            exact hv1 (by rw [hval]; exact Finset.mem_image_of_mem e (Finset.mem_univ r₂))
          · simp only [φ1, Function.comp_apply, Function.update_of_ne hq] at hval
            exact hq (he hval)
        subst hr_eq
        have hupd_inj : Function.Injective (Function.update e r₁ v₁) := by
          intro a b hab
          by_cases ha : a = r₁ <;> by_cases hb : b = r₁
          · rw [ha, hb]
          · subst ha; simp only [Function.update_self, Function.update_of_ne hb] at hab
            exact absurd (hab ▸ Finset.mem_image_of_mem e (Finset.mem_univ b)) hv1
          · subst hb; simp only [Function.update_self, Function.update_of_ne ha] at hab
            exact absurd (hab.symm ▸ Finset.mem_image_of_mem e (Finset.mem_univ a)) hv1
          · simp only [Function.update_of_ne ha, Function.update_of_ne hb] at hab
            exact he hab
        have hπ : π₁ = π₂ := Equiv.ext fun j => hupd_inj (congr_fun h j)
        subst hπ
        rfl
      have hφ1_img : Finset.image φ1 dom = F1 := by
        ext f
        simp only [Finset.mem_image, F1, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨r, v, π⟩, hmem, rfl⟩
          have hv : v ∉ S := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).1
          have hupd_inj : Function.Injective (Function.update e r v) := by
            intro a b hab
            by_cases ha : a = r <;> by_cases hb : b = r
            · rw [ha, hb]
            · subst ha; simp only [Function.update_self, Function.update_of_ne hb] at hab
              exact absurd (hab ▸ Finset.mem_image_of_mem e (Finset.mem_univ b)) hv
            · subst hb; simp only [Function.update_self, Function.update_of_ne ha] at hab
              exact absurd (hab.symm ▸ Finset.mem_image_of_mem e (Finset.mem_univ a)) hv
            · simp only [Function.update_of_ne ha, Function.update_of_ne hb] at hab
              exact he hab
          refine ⟨hupd_inj.comp π.injective, ?_⟩
          have hfilter : Finset.univ.filter (fun i : Fin k => φ1 (r, v, π) i ∉ S) = {π⁻¹ r} := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, φ1,
              Function.comp_apply]
            constructor
            · intro hi
              by_contra hne
              have hne' : π i ≠ r := fun h => hne (by simp [← h])
              rw [Function.update_of_ne hne'] at hi
              exact hi (Finset.mem_image_of_mem e (Finset.mem_univ _))
            · rintro rfl; simp [hv]
          simp [outCard, hfilter]
        · rintro ⟨hfinj, hout⟩
          obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hout
          have hi₀_mem : i₀ ∈ Finset.univ.filter (fun i : Fin k => f i ∉ S) :=
            hi₀ ▸ Finset.mem_singleton_self i₀
          have hfi₀ : f i₀ ∉ S := (Finset.mem_filter.mp hi₀_mem).2
          have hfi_in : ∀ i : Fin k, i ≠ i₀ → f i ∈ S := by
            intro i hne
            by_contra hnot
            have hm : i ∈ Finset.univ.filter (fun j : Fin k => f j ∉ S) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnot⟩
            rw [hi₀, Finset.mem_singleton] at hm
            exact hne hm
          have hfS_sub : (Finset.univ.erase i₀).image f ⊆ S := by
            intro x hx
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
            exact hfi_in i (Finset.ne_of_mem_erase hi)
          have hScard : S.card = k := by
            rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]
          have hcard_fS : ((Finset.univ.erase i₀).image f).card = k - 1 := by
            rw [Finset.card_image_of_injective _ hfinj, Finset.card_erase_of_mem (Finset.mem_univ i₀),
              Finset.card_univ, Fintype.card_fin]
          have hk_pos : 1 ≤ k := Nat.succ_le_of_lt i₀.pos
          have hsdiff_card : (S \ (Finset.univ.erase i₀).image f).card = 1 := by
            have hunion := Finset.sdiff_union_of_subset hfS_sub
            have hdisj_s : Disjoint (S \ (Finset.univ.erase i₀).image f) ((Finset.univ.erase i₀).image f) :=
              Finset.sdiff_disjoint
            have hcard_u := congrArg Finset.card hunion
            rw [Finset.card_union_of_disjoint hdisj_s, hcard_fS, hScard] at hcard_u
            omega
          obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsdiff_card
          have hu_mem : u ∈ S \ (Finset.univ.erase i₀).image f := hu ▸ Finset.mem_singleton_self u
          obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hu_mem).1
          have her_notin : e r ∉ (Finset.univ.erase i₀).image f := (Finset.mem_sdiff.mp hu_mem).2
          have hf_in_upd : ∀ i : Fin k, ∃ j : Fin k, Function.update e r (f i₀) j = f i := by
            intro i
            by_cases hi : i = i₀
            · subst hi; exact ⟨r, by simp⟩
            · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hfi_in i hi)
              have hjr : j ≠ r := fun h => by
                subst h
                exact her_notin (hj ▸ Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩))
              exact ⟨j, by simp [hjr, hj]⟩
          choose p hp using hf_in_upd
          have hp_inj : Function.Injective p := fun a b hab =>
            hfinj ((hp a).symm.trans ((congrArg (Function.update e r (f i₀)) hab).trans (hp b)))
          have hp_bij : Function.Bijective p := Finite.injective_iff_bijective.mp hp_inj
          refine ⟨⟨r, f i₀, Equiv.ofBijective p hp_bij⟩, ?_, funext hp⟩
          simp [dom, hfi₀]
      rw [← hφ1_img, Finset.sum_image hφ1_inj]
      have hterm1 : ∀ (r : Fin k) (v : Fin m) (hv : v ∈ Sᶜ) (π : Equiv.Perm (Fin k)),
          (A₀.submatrix e (φ1 (r, v, π))).det * Mavg (φ1 (r, v, π)) e =
            (A₀.submatrix e (Function.update e r v)).det * (-Mavg e e / ((m - k : ℕ) : ℝ)) := by
        intro r v hv π
        have hdet : (A₀.submatrix e (Function.update e r v ∘ π)).det =
            (Equiv.Perm.sign π : ℝ) * (A₀.submatrix e (Function.update e r v)).det := by
          have hsub : A₀.submatrix e (Function.update e r v ∘ π) =
              (A₀.submatrix e (Function.update e r v)).submatrix id π := rfl
          rw [hsub, Matrix.det_permute']
        simp only [φ1]
        rw [hdet, hMavg_perm_left, hMavg_shift he r (Finset.mem_compl.mp hv)]
        have hsign : (Equiv.Perm.sign π : ℝ) * (Equiv.Perm.sign π : ℝ) = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
        calc ((Equiv.Perm.sign π : ℝ) * (A₀.submatrix e (Function.update e r v)).det) *
              ((Equiv.Perm.sign π : ℝ) * (-Mavg e e / ((m - k : ℕ) : ℝ)))
            = ((Equiv.Perm.sign π : ℝ) * (Equiv.Perm.sign π : ℝ)) *
              ((A₀.submatrix e (Function.update e r v)).det * (-Mavg e e / ((m - k : ℕ) : ℝ))) := by ring
          _ = (A₀.submatrix e (Function.update e r v)).det * (-Mavg e e / ((m - k : ℕ) : ℝ)) := by
              rw [hsign, one_mul]
      dsimp only [dom]
      rw [Finset.sum_product]
      simp_rw [Finset.sum_product]
      have hr_sum : ∀ r : Fin k,
          (∑ v ∈ Sᶜ, ∑ π : Equiv.Perm (Fin k),
            (A₀.submatrix e (φ1 (r, v, π))).det * Mavg (φ1 (r, v, π)) e) =
          (k.factorial : ℝ) * ((A₀.submatrix e e).det * (Mavg e e / ((m - k : ℕ) : ℝ))) := by
        intro r
        have hv_inner : ∀ v ∈ Sᶜ,
            (∑ π : Equiv.Perm (Fin k),
              (A₀.submatrix e (φ1 (r, v, π))).det * Mavg (φ1 (r, v, π)) e) =
            (k.factorial : ℝ) *
              ((A₀.submatrix e (Function.update e r v)).det * (-Mavg e e / ((m - k : ℕ) : ℝ))) := by
          intro v hv
          simp_rw [hterm1 r v hv, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.sum_congr rfl hv_inner, ← Finset.mul_sum, ← Finset.sum_mul]
        have hA_col_all : ∑ v : Fin m, (A₀.submatrix e (Function.update e r v)).det = 0 := by
          have hupd : ∀ v : Fin m,
              A₀.submatrix e (Function.update e r v) =
                (A₀.submatrix e e).updateCol r (fun i => A₀ (e i) v) := by
            intro v; ext i j
            by_cases hjr : j = r <;> simp [hjr]
          simp_rw [hupd, ← det_updateCol_finset_sum]
          have hcol0 : (∑ v ∈ (Finset.univ : Finset (Fin m)), fun i : Fin k => A₀ (e i) v) = 0 := by
            funext i
            have h0 : (A₀ * onesMat m) (e i) 0 = 0 := by rw [hA₀_row]; rfl
            simpa [Finset.sum_apply, Matrix.mul_apply, onesMat] using h0
          rw [hcol0]
          exact Matrix.det_eq_zero_of_column_eq_zero r (fun _ => by simp)
        have hA_col_S : ∑ v ∈ S, (A₀.submatrix e (Function.update e r v)).det =
            (A₀.submatrix e e).det := by
          rw [Finset.sum_eq_single (e r)]
          · rw [Function.update_eq_self]
          · intro v hv hne
            obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hv
            have hr' : r' ≠ r := fun h => hne (congrArg e h)
            have hni : ¬Function.Injective (Function.update e r (e r')) := by
              intro hinj
              have heq : Function.update e r (e r') r = Function.update e r (e r') r' := by
                rw [Function.update_self, Function.update_of_ne hr']
              exact hr' (hinj heq).symm
            exact det_submatrix_eq_zero_of_not_injective_col A₀ e hni
          · intro hmem; exact absurd (Finset.mem_image_of_mem e (Finset.mem_univ r)) hmem
        have hsplitA : (∑ v : Fin m, (A₀.submatrix e (Function.update e r v)).det) =
            (∑ v ∈ S, (A₀.submatrix e (Function.update e r v)).det) +
            (∑ v ∈ Sᶜ, (A₀.submatrix e (Function.update e r v)).det) := by
          rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
        have hcompl_eq : ∑ v ∈ Sᶜ, (A₀.submatrix e (Function.update e r v)).det =
            -(A₀.submatrix e e).det := by
          linarith
        rw [hcompl_eq]
        ring
      simp_rw [hr_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hred, hF0, hF1, hMavg_diag he]
    have hbinom_rel : (m - k : ℕ) * m.choose k = m * d.choose k := by
      have hf1 : m.choose k * k.factorial * (m - k).factorial = m.factorial :=
        Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ m)
      have hf2 : d.choose k * k.factorial * (d - k).factorial = d.factorial :=
        Nat.choose_mul_factorial_mul_factorial hk
      have hsub_eq : m - k = (d - k) + 1 := by omega
      have hfac_mk : (m - k).factorial = (m - k) * (d - k).factorial := by
        rw [hsub_eq, Nat.factorial_succ, ← hsub_eq]
      have hfac_m : m.factorial = m * d.factorial := Nat.factorial_succ d
      have hmul1 : ((m - k) * m.choose k) * (k.factorial * (d - k).factorial) =
          (m * d.choose k) * (k.factorial * (d - k).factorial) := by
        calc ((m - k) * m.choose k) * (k.factorial * (d - k).factorial)
            = m.choose k * k.factorial * ((m - k) * (d - k).factorial) := by ring
          _ = m.choose k * k.factorial * (m - k).factorial := by rw [← hfac_mk]
          _ = m.factorial := hf1
          _ = m * d.factorial := hfac_m
          _ = m * (d.choose k * k.factorial * (d - k).factorial) := by rw [← hf2]
          _ = (m * d.choose k) * (k.factorial * (d - k).factorial) := by ring
      exact Nat.eq_of_mul_eq_mul_right
        (Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (d - k))) hmul1
    have hbinom_real : ((m - k : ℕ) : ℝ) * (m.choose k : ℝ) = (m : ℝ) * (d.choose k : ℝ) := by
      exact_mod_cast hbinom_rel
    have hmk_add : ((m - k : ℕ) : ℝ) + (k : ℝ) = (m : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (by omega : k ≤ m)
    have hkey : (1 + (k : ℝ) / ((m - k : ℕ) : ℝ)) * (sumMinors k B₀ / (m.choose k : ℝ)) =
        sumMinors k B₀ / (d.choose k : ℝ) := by
      rw [one_add_div hmk_ne, hmk_add, div_mul_div_comm, hbinom_real,
        mul_comm (m : ℝ) (sumMinors k B₀), mul_comm (m : ℝ) (d.choose k : ℝ),
        mul_div_mul_right _ _ hm_pos.ne']
    calc (k.factorial : ℝ) * (A₀.submatrix e e).det * (sumMinors k B₀ / (m.choose k : ℝ)) +
          (k.factorial : ℝ) * ((k : ℝ) / ((m - k : ℕ) : ℝ)) * (A₀.submatrix e e).det *
            (sumMinors k B₀ / (m.choose k : ℝ))
        = (k.factorial : ℝ) * (A₀.submatrix e e).det *
          ((1 + (k : ℝ) / ((m - k : ℕ) : ℝ)) * (sumMinors k B₀ / (m.choose k : ℝ))) := by ring
      _ = (k.factorial : ℝ) * (A₀.submatrix e e).det * (sumMinors k B₀ / (d.choose k : ℝ)) := by
          rw [hkey]
  -- Now sum `dinner_sum` over all `e : Fin k → Fin m` and divide by `(k!)^2`
  have htotal : (k.factorial : ℝ) ^ 2 *
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin m), sumMinors k (A₀ * Cmat σ)) =
      (k.factorial : ℝ) ^ 2 * (sumMinors k A₀ * sumMinors k B₀ / (d.choose k : ℝ)) := by
    have hlhs : (k.factorial : ℝ) ^ 2 *
        ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin m), sumMinors k (A₀ * Cmat σ)) =
        ∑ e : Fin k → Fin m, ∑ f : Fin k → Fin m, (A₀.submatrix e f).det * Mavg f e := by
      have hcb_σ : ∀ σ : Equiv.Perm (Fin m),
          (k.factorial : ℝ) ^ 2 * sumMinors k (A₀ * Cmat σ) =
            ∑ e : Fin k → Fin m, ∑ f : Fin k → Fin m,
              (A₀.submatrix e f).det * ((Cmat σ).submatrix f e).det := by
        intro σ
        rw [sq, mul_assoc, ← tupleMinorSum_eq_factorial_mul_sumMinors]
        unfold tupleMinorSum
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        have hsub : (A₀ * Cmat σ).submatrix e e = A₀.submatrix e id * (Cmat σ).submatrix id e := by
          ext i j; simp [Matrix.mul_apply]
        rw [hsub, ← cauchy_binet_tuples]
        rfl
      calc (k.factorial : ℝ) ^ 2 *
            ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
              ∑ σ : Equiv.Perm (Fin m), sumMinors k (A₀ * Cmat σ))
          = (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
              ∑ σ : Equiv.Perm (Fin m), (k.factorial : ℝ) ^ 2 * sumMinors k (A₀ * Cmat σ) := by
              rw [← mul_assoc, mul_comm ((k.factorial : ℝ) ^ 2), mul_assoc, Finset.mul_sum]
        _ = (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
              ∑ σ : Equiv.Perm (Fin m), ∑ e : Fin k → Fin m, ∑ f : Fin k → Fin m,
                (A₀.submatrix e f).det * ((Cmat σ).submatrix f e).det := by
              simp_rw [hcb_σ]
        _ = ∑ e : Fin k → Fin m, ∑ f : Fin k → Fin m, (A₀.submatrix e f).det * Mavg f e := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun f _ => ?_
              simp only [Mavg, Finset.mul_sum, mul_left_comm]
    rw [hlhs]
    have he_each : ∀ e : Fin k → Fin m,
        (∑ f : Fin k → Fin m, (A₀.submatrix e f).det * Mavg f e) =
          (k.factorial : ℝ) * (A₀.submatrix e e).det * (sumMinors k B₀ / (d.choose k : ℝ)) := by
      intro e
      by_cases he : Function.Injective e
      · exact dinner_sum he
      · have h1 : ∀ f, (A₀.submatrix e f).det = 0 :=
          fun f => det_submatrix_eq_zero_of_not_injective_row A₀ he f
        simp [h1]
    simp_rw [he_each]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    change (k.factorial : ℝ) * tupleMinorSum k A₀ * (sumMinors k B₀ / (d.choose k : ℝ)) = _
    rw [tupleMinorSum_eq_factorial_mul_sumMinors]
    ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hkfac_ne) htotal

end MinorsQuadrature

/-! ### Section 4: Multiplicative quadrature (C2), additive quadrature (C1), and real-rootedness (C3, C4) -/

section MainQuadrature

lemma monic_and_deg_of_charpoly_factor {d : ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {c : ℝ} {p : ℝ[X]} (hp : M.charpoly = (X - C c) * p) :
    p.Monic ∧ p.natDegree = d := by
  have hM_monic : M.charpoly.Monic := Matrix.charpoly_monic M
  have hM_deg : M.charpoly.natDegree = d + 1 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hp_ne : p ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hp
    exact hM_monic.ne_zero hp
  have hp_monic : p.Monic := by
    have hlc := congrArg Polynomial.leadingCoeff hp
    rw [hM_monic.leadingCoeff, Polynomial.leadingCoeff_mul,
      (Polynomial.monic_X_sub_C c).leadingCoeff, one_mul] at hlc
    exact hlc.symm
  have hp_deg : p.natDegree = d := by
    rw [hp, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero c) hp_ne,
      Polynomial.natDegree_X_sub_C] at hM_deg
    omega
  exact ⟨hp_monic, hp_deg⟩

lemma ffCoeff_eq_sumMinors_of_X_mul {d : ℕ} {M₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {p : ℝ[X]} (hcp : M₀.charpoly = X * p) {k : ℕ} (hk : k ≤ d) :
    ffCoeff d p k = sumMinors k M₀ := by
  have h1 := Matrix.charpoly_coeff_eq_sum_minors M₀ k (by simp; omega)
  rw [Fintype.card_fin] at h1
  have hidx : d + 1 - k = (d - k) + 1 := by omega
  rw [hidx, hcp, Polynomial.coeff_X_mul] at h1
  unfold ffCoeff sumMinors
  rw [h1, ← mul_assoc]
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  rw [hsign, one_mul]

/-- Multiplicative quadrature (part 2 of Lemma 2.5) in dimension `m = d + 1`. -/
lemma expCharpolyMul_quadrature (d : ℕ)
    (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (a b : ℝ) (hA1 : A *ᵥ onesVec (d + 1) = a • onesVec (d + 1))
    (hB1 : B *ᵥ onesVec (d + 1) = b • onesVec (d + 1))
    (pA pB : ℝ[X]) (hpA : A.charpoly = (X - C a) * pA) (hpB : B.charpoly = (X - C b) * pB) :
    expCharpolyMul A B = (X - C (a * b)) * ffMul d pA pB := by
  let m := d + 1
  let A₀ : Matrix (Fin m) (Fin m) ℝ := A - (a / (m : ℝ)) • onesMat m
  let B₀ : Matrix (Fin m) (Fin m) ℝ := B - (b / (m : ℝ)) • onesMat m
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hAJ : A * onesMat m = a • onesMat m := mul_onesMat_of_mulVec hA1
  have hJA : onesMat m * A = a • onesMat m := onesMat_mul_of_symm hA hAJ
  have hBJ : B * onesMat m = b • onesMat m := mul_onesMat_of_mulVec hB1
  have hJB : onesMat m * B = b • onesMat m := onesMat_mul_of_symm hB hBJ
  have hA₀J : A₀ * onesMat m = 0 := by
    simp only [A₀, Matrix.sub_mul, Matrix.smul_mul, hAJ, onesMat_mul_onesMat, smul_smul]
    rw [div_mul_cancel₀ a hm_ne, sub_self]
  have hB₀J : B₀ * onesMat m = 0 := by
    simp only [B₀, Matrix.sub_mul, Matrix.smul_mul, hBJ, onesMat_mul_onesMat, smul_smul]
    rw [div_mul_cancel₀ b hm_ne, sub_self]
  have hJB₀ : onesMat m * B₀ = 0 := by
    simp only [B₀, Matrix.mul_sub, Matrix.mul_smul, hJB, onesMat_mul_onesMat, smul_smul]
    rw [div_mul_cancel₀ b hm_ne, sub_self]
  -- `A₀.charpoly = X * pA` and `B₀.charpoly = X * pB`
  have hm_cast : (m : ℝ) = (d : ℝ) + 1 := by simp [m]
  have hcpA₀ : A₀.charpoly = X * pA := by
    have hshift := charpoly_add_smul_onesMat d A₀ hA₀J a
    have hadd : A₀ + (a / (d + 1 : ℝ)) • onesMat (d + 1) = A := by
      simpa only [A₀, hm_cast] using sub_add_cancel A ((a / ((d : ℝ) + 1)) • onesMat (d + 1))
    rw [hadd, hpA] at hshift
    exact mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero a)
      (calc (X - C a) * A₀.charpoly = X * ((X - C a) * pA) := hshift.symm
        _ = (X - C a) * (X * pA) := by ring)
  have hcpB₀ : B₀.charpoly = X * pB := by
    have hshift := charpoly_add_smul_onesMat d B₀ hB₀J b
    have hadd : B₀ + (b / (d + 1 : ℝ)) • onesMat (d + 1) = B := by
      simpa only [B₀, hm_cast] using sub_add_cancel B ((b / ((d : ℝ) + 1)) • onesMat (d + 1))
    rw [hadd, hpB] at hshift
    exact mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero b)
      (calc (X - C b) * B₀.charpoly = X * ((X - C b) * pB) := hshift.symm
        _ = (X - C b) * (X * pB) := by ring)
  -- Decomposition `A * P_σ * B * P_σᵀ = A₀ * P_σ * B₀ * P_σᵀ + (a*b / m) • onesMat m`
  have hdecomp : ∀ σ : Equiv.Perm (Fin m),
      A * permMat σ * B * (permMat σ)ᵀ =
        A₀ * permMat σ * B₀ * (permMat σ)ᵀ + (a * b / (m : ℝ)) • onesMat m := by
    intro σ
    have hA_eq : A = A₀ + (a / (m : ℝ)) • onesMat m := (sub_add_cancel _ _).symm
    have hB_eq : permMat σ * B * (permMat σ)ᵀ =
        permMat σ * B₀ * (permMat σ)ᵀ + (b / (m : ℝ)) • onesMat m := by
      have hb : B = B₀ + (b / (m : ℝ)) • onesMat m := (sub_add_cancel _ _).symm
      conv_lhs => rw [hb]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, conj_permMat_onesMat]
    calc A * permMat σ * B * (permMat σ)ᵀ
        = A * (permMat σ * B * (permMat σ)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = (A₀ + (a / (m : ℝ)) • onesMat m) *
          (permMat σ * B₀ * (permMat σ)ᵀ + (b / (m : ℝ)) • onesMat m) := by
            rw [← hB_eq, ← hA_eq]
      _ = A₀ * permMat σ * B₀ * (permMat σ)ᵀ + (a * b / (m : ℝ)) • onesMat m := by
            rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
            have hz1 : A₀ * ((b / (m : ℝ)) • onesMat m) = 0 := by
              rw [Matrix.mul_smul, hA₀J, smul_zero]
            have hz2 : ((a / (m : ℝ)) • onesMat m) * (permMat σ * B₀ * (permMat σ)ᵀ) = 0 := by
              rw [Matrix.smul_mul]
              have h1 : onesMat m * (permMat σ * B₀ * (permMat σ)ᵀ) = 0 := by
                calc onesMat m * (permMat σ * B₀ * (permMat σ)ᵀ)
                    = (permMat σ * onesMat m * (permMat σ)ᵀ) * (permMat σ * B₀ * (permMat σ)ᵀ) := by
                        rw [conj_permMat_onesMat]
                  _ = permMat σ * (onesMat m * ((permMat σ)ᵀ * permMat σ) * B₀) * (permMat σ)ᵀ := by
                        simp only [Matrix.mul_assoc]
                  _ = 0 := by
                        have htp : (permMat σ)ᵀ * permMat σ = 1 := by
                          have htr : (permMat σ)ᵀ = permMat σ⁻¹ := by
                            ext i j; simp [permMat_apply', eq_comm, σ.eq_symm_apply]
                          rw [htr, ← permMat_mul_eq, mul_inv_cancel]
                          ext i j; simp [permMat_apply', Matrix.one_apply, eq_comm]
                        rw [htp, Matrix.mul_one, hJB₀, Matrix.mul_zero, Matrix.zero_mul]
              rw [h1, smul_zero]
            have hJJ : ((a / (m : ℝ)) • onesMat m) * ((b / (m : ℝ)) • onesMat m) =
                (a * b / (m : ℝ)) • onesMat m := by
              rw [Matrix.smul_mul, Matrix.mul_smul, onesMat_mul_onesMat, smul_smul, smul_smul]
              congr 1
              field_simp [hm_ne]
            rw [hz1, hz2, hJJ, add_zero, zero_add]
            simp only [Matrix.mul_assoc]
  -- Shift identity on `expCharpolyMul`
  have hexp_shift : X * expCharpolyMul A B = (X - C (a * b)) * expCharpolyMul A₀ B₀ := by
    unfold expCharpolyMul
    rw [permAvg_mul_left, permAvg_mul_left]
    congr 1; funext σ
    rw [hdecomp σ, hm_cast]
    refine charpoly_add_smul_onesMat d (A₀ * permMat σ * B₀ * (permMat σ)ᵀ) ?_ (a * b)
    calc (A₀ * permMat σ * B₀ * (permMat σ)ᵀ) * onesMat m
        = A₀ * permMat σ * (B₀ * ((permMat σ)ᵀ * onesMat m)) := by simp only [Matrix.mul_assoc]
      _ = 0 := by
          have hpJ : (permMat σ)ᵀ * onesMat m = onesMat m := by
            ext i j
            simp only [Matrix.mul_apply, Matrix.transpose_apply, permMat_apply', onesMat,
              Matrix.of_apply, mul_one]
            rw [Finset.sum_eq_single (σ⁻¹ i)]
            · simp
            · intro b _ hb
              have hne : i ≠ σ b := fun h => hb (by simp [h])
              simp [hne]
            · intro hmem; exact absurd (Finset.mem_univ _) hmem
          rw [hpJ, hB₀J, Matrix.mul_zero]
  -- Prove `expCharpolyMul A₀ B₀ = X * ffMul d pA pB` coefficient by coefficient
  have hexp₀ : expCharpolyMul A₀ B₀ = X * ffMul d pA pB := by
    ext j
    by_cases hj0 : j = 0
    · subst hj0
      rw [Polynomial.coeff_X_mul_zero]
      unfold expCharpolyMul permAvg
      rw [Polynomial.coeff_smul, smul_eq_mul, Polynomial.finsetSum_coeff]
      suffices ∀ σ : Equiv.Perm (Fin m),
          ((A₀ * permMat σ * B₀ * (permMat σ)ᵀ).charpoly).coeff 0 = 0 by
        simp [this]
      intro σ
      have hdet0 : (A₀ * permMat σ * B₀ * (permMat σ)ᵀ).det = 0 := by
        by_contra hne
        have hisUnit : IsUnit (A₀ * permMat σ * B₀ * (permMat σ)ᵀ).det := Ne.isUnit hne
        have hmul0 : (A₀ * permMat σ * B₀ * (permMat σ)ᵀ) * onesMat m = 0 := by
          have hpJ : (permMat σ)ᵀ * onesMat m = onesMat m := by
            ext i j
            simp only [Matrix.mul_apply, Matrix.transpose_apply, permMat_apply', onesMat,
              Matrix.of_apply, mul_one]
            rw [Finset.sum_eq_single (σ⁻¹ i)]
            · simp
            · intro b _ hb
              have hne : i ≠ σ b := fun h => hb (by simp [h])
              simp [hne]
            · intro hmem; exact absurd (Finset.mem_univ _) hmem
          calc (A₀ * permMat σ * B₀ * (permMat σ)ᵀ) * onesMat m
              = A₀ * permMat σ * (B₀ * ((permMat σ)ᵀ * onesMat m)) := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hpJ, hB₀J, Matrix.mul_zero]
        have hzero_eq := congrArg (fun Q => (A₀ * permMat σ * B₀ * (permMat σ)ᵀ)⁻¹ * Q) hmul0
        rw [Matrix.mul_zero, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hisUnit, Matrix.one_mul] at hzero_eq
        have h10 : (onesMat m) 0 0 = 0 := by rw [hzero_eq]; rfl
        norm_num [onesMat] at h10
      have hsign := Matrix.det_eq_sign_charpoly_coeff (A₀ * permMat σ * B₀ * (permMat σ)ᵀ)
      rw [hdet0, Fintype.card_fin] at hsign
      have hpow_ne : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
      exact (mul_eq_zero.mp hsign.symm).resolve_left hpow_ne
    · by_cases hle : j ≤ d + 1
      · let k := d + 1 - j
        have hk : k ≤ d := by omega
        have hj_eq : j = d + 1 - k := by omega
        rw [hj_eq]
        -- LHS coefficient at `d + 1 - k`
        have hlhs : (expCharpolyMul A₀ B₀).coeff (d + 1 - k) =
            (-1 : ℝ) ^ k * (sumMinors k A₀ * sumMinors k B₀ / (d.choose k : ℝ)) := by
          unfold expCharpolyMul permAvg
          rw [Polynomial.coeff_smul, smul_eq_mul, Polynomial.finsetSum_coeff]
          have hcp_k : ∀ σ : Equiv.Perm (Fin m),
              ((A₀ * permMat σ * B₀ * (permMat σ)ᵀ).charpoly).coeff (d + 1 - k) =
                (-1 : ℝ) ^ k * sumMinors k (A₀ * permMat σ * B₀ * (permMat σ)ᵀ) := by
            intro σ
            have h := Matrix.charpoly_coeff_eq_sum_minors
              (A₀ * permMat σ * B₀ * (permMat σ)ᵀ) k (by simp [m]; omega)
            simpa [m, Fintype.card_fin, sumMinors] using h
          simp_rw [hcp_k, ← Finset.mul_sum]
          rw [← mul_assoc, mul_comm ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) ((-1 : ℝ) ^ k), mul_assoc]
          congr 1
          exact avg_sumMinors_mul_zero_sum d A₀ B₀ hA₀J hJB₀ k hk
        -- RHS coefficient at `d + 1 - k = (d - k) + 1`
        have hrhs : (X * ffMul d pA pB).coeff (d + 1 - k) =
            (-1 : ℝ) ^ k * ffCoeff d pA k * ffCoeff d pB k / (d.choose k : ℝ) := by
          have hidx : d + 1 - k = (d - k) + 1 := by omega
          rw [hidx, Polynomial.coeff_X_mul]
          unfold ffMul
          rw [Polynomial.finsetSum_coeff]
          rw [Finset.sum_eq_single k]
          · simp
          · intro i hi hne
            have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hne' : d - i ≠ d - k := by omega
            simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne'.symm]
          · intro hmem; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hmem
        rw [hlhs, hrhs, ffCoeff_eq_sumMinors_of_X_mul hcpA₀ hk,
          ffCoeff_eq_sumMinors_of_X_mul hcpB₀ hk]
        ring
      · -- `j > d + 1`: both sides have degree `≤ d + 1`, so `.coeff j = 0`
        have hj_gt : d + 1 < j := by omega
        have hlhs0 : (expCharpolyMul A₀ B₀).coeff j = 0 := by
          unfold expCharpolyMul permAvg
          rw [Polynomial.coeff_smul, smul_eq_mul, Polynomial.finsetSum_coeff]
          have h0 : ∀ σ : Equiv.Perm (Fin m),
              ((A₀ * permMat σ * B₀ * (permMat σ)ᵀ).charpoly).coeff j = 0 := by
            intro σ
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
            exact hj_gt
          simp [h0]
        have hrhs0 : (X * ffMul d pA pB).coeff j = 0 := by
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          rw [Polynomial.coeff_X_mul]
          unfold ffMul
          rw [Polynomial.finsetSum_coeff]
          refine Finset.sum_eq_zero fun i hi => ?_
          have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hne : j' ≠ d - i := by omega
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
        rw [hlhs0, hrhs0]
  rw [hexp₀] at hexp_shift
  exact mul_left_cancel₀ Polynomial.X_ne_zero
    (calc X * expCharpolyMul A B = (X - C (a * b)) * (X * ffMul d pA pB) := hexp_shift
      _ = X * ((X - C (a * b)) * ffMul d pA pB) := by ring)

/-- Binomial cancellation identity driving the `t → 0` rescaling of `ffMul` to `ffAdd`. -/
lemma alternating_choose_sum_Icc (d i j s : ℕ) (his : i ≤ s) (hjs : j ≤ s) (hsd : s ≤ d) :
    (∑ r ∈ Finset.Icc (max i j) s,
        (-1 : ℝ) ^ r * ((d - i).choose (r - i) : ℝ) * ((d - j).choose (r - j) : ℝ) *
          ((d - r).choose (s - r) : ℝ) / (d.choose r : ℝ)) =
      if i + j < s then 0
      else if i + j = s then
        (-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
          ((d.factorial : ℝ) * ((d - s).factorial : ℝ))
      else
        (-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
          ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
          ((j.factorial : ℝ) / ((s - i).factorial : ℝ)) *
          (i.choose (j - (s - i)) : ℝ) := by
  let pref : ℝ := ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
      ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
      ((j.factorial : ℝ) / ((s - i).factorial : ℝ))
  have hterm_eq : ∀ r ∈ Finset.Icc (max i j) s,
      (-1 : ℝ) ^ r * ((d - i).choose (r - i) : ℝ) * ((d - j).choose (r - j) : ℝ) *
          ((d - r).choose (s - r) : ℝ) / (d.choose r : ℝ) =
        pref * ((-1 : ℝ) ^ r * ((s - i).choose (r - i) : ℝ) * (r.choose j : ℝ)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hir : i ≤ r := le_trans (le_max_left i j) hr.1
    have hjr : j ≤ r := le_trans (le_max_right i j) hr.1
    have hrs : r ≤ s := hr.2
    have hrd : r ≤ d := le_trans hrs hsd
    have h1 : ((d - i).choose (r - i) : ℝ) * ((r - i).factorial : ℝ) * ((d - r).factorial : ℝ) =
        ((d - i).factorial : ℝ) := by
      have hsub : (d - i) - (r - i) = d - r := by omega
      have hn := Nat.choose_mul_factorial_mul_factorial (by omega : r - i ≤ d - i)
      rw [hsub] at hn; exact_mod_cast hn
    have h2 : ((d - j).choose (r - j) : ℝ) * ((r - j).factorial : ℝ) * ((d - r).factorial : ℝ) =
        ((d - j).factorial : ℝ) := by
      have hsub : (d - j) - (r - j) = d - r := by omega
      have hn := Nat.choose_mul_factorial_mul_factorial (by omega : r - j ≤ d - j)
      rw [hsub] at hn; exact_mod_cast hn
    have h3 : ((d - r).choose (s - r) : ℝ) * ((s - r).factorial : ℝ) * ((d - s).factorial : ℝ) =
        ((d - r).factorial : ℝ) := by
      have hsub : (d - r) - (s - r) = d - s := by omega
      have hn := Nat.choose_mul_factorial_mul_factorial (by omega : s - r ≤ d - r)
      rw [hsub] at hn; exact_mod_cast hn
    have h4 : (d.choose r : ℝ) * (r.factorial : ℝ) * ((d - r).factorial : ℝ) = (d.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hrd
    have h5 : (r.choose j : ℝ) * (j.factorial : ℝ) * ((r - j).factorial : ℝ) = (r.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjr
    have h6 : ((s - i).choose (r - i) : ℝ) * ((r - i).factorial : ℝ) * ((s - r).factorial : ℝ) =
        ((s - i).factorial : ℝ) := by
      have hsub : (s - i) - (r - i) = s - r := by omega
      have hn := Nat.choose_mul_factorial_mul_factorial (by omega : r - i ≤ s - i)
      rw [hsub] at hn; exact_mod_cast hn
    have hdfac_ne : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hdsfac_ne : ((d - s).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hsifac_ne : ((s - i).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hdchoose_ne : (d.choose r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hrd).ne'
    have hrifac_ne : ((r - i).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hrjfac_ne : ((r - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hsrfac_ne : ((s - r).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hdrfac_ne : ((d - r).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hden_ne : (d.factorial : ℝ) * ((d - s).factorial : ℝ) * ((s - i).factorial : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hdfac_ne hdsfac_ne) hsifac_ne
    have hextra_ne : ((r - i).factorial : ℝ) * ((r - j).factorial : ℝ) * ((s - r).factorial : ℝ) *
        (((d - r).factorial : ℝ) * ((d - r).factorial : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hrifac_ne hrjfac_ne) hsrfac_ne) (mul_ne_zero hdrfac_ne hdrfac_ne)
    rw [div_eq_iff hdchoose_ne]
    apply mul_right_cancel₀ hden_ne
    have hrhs_simp : pref * ((-1 : ℝ) ^ r * ((s - i).choose (r - i) : ℝ) * (r.choose j : ℝ)) *
        (d.choose r : ℝ) * ((d.factorial : ℝ) * ((d - s).factorial : ℝ) * ((s - i).factorial : ℝ)) =
        ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) * (j.factorial : ℝ) *
          ((-1 : ℝ) ^ r * ((s - i).choose (r - i) : ℝ) * (r.choose j : ℝ)) * (d.choose r : ℝ) := by
      dsimp only [pref]
      field_simp [hdfac_ne, hdsfac_ne, hsifac_ne]
    rw [hrhs_simp]
    apply mul_right_cancel₀ hextra_ne
    calc (-1 : ℝ) ^ r * ((d - i).choose (r - i) : ℝ) * ((d - j).choose (r - j) : ℝ) *
            ((d - r).choose (s - r) : ℝ) *
            ((d.factorial : ℝ) * ((d - s).factorial : ℝ) * ((s - i).factorial : ℝ)) *
            (((r - i).factorial : ℝ) * ((r - j).factorial : ℝ) * ((s - r).factorial : ℝ) *
              (((d - r).factorial : ℝ) * ((d - r).factorial : ℝ)))
        = (-1 : ℝ) ^ r *
            (((d - i).choose (r - i) : ℝ) * ((r - i).factorial : ℝ) * ((d - r).factorial : ℝ)) *
            (((d - j).choose (r - j) : ℝ) * ((r - j).factorial : ℝ) * ((d - r).factorial : ℝ)) *
            (((d - r).choose (s - r) : ℝ) * ((s - r).factorial : ℝ) * ((d - s).factorial : ℝ)) *
            (d.factorial : ℝ) * ((s - i).factorial : ℝ) := by ring
      _ = (-1 : ℝ) ^ r * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) *
            ((d - r).factorial : ℝ) * (d.factorial : ℝ) * ((s - i).factorial : ℝ) := by
            rw [h1, h2, h3]
      _ = (-1 : ℝ) ^ r * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) *
            ((d - r).factorial : ℝ) *
            ((d.choose r : ℝ) * (r.factorial : ℝ) * ((d - r).factorial : ℝ)) *
            (((s - i).choose (r - i) : ℝ) * ((r - i).factorial : ℝ) * ((s - r).factorial : ℝ)) := by
            rw [← h4, ← h6]
      _ = (-1 : ℝ) ^ r * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) *
            ((d - r).factorial : ℝ) *
            ((d.choose r : ℝ) * ((r.choose j : ℝ) * (j.factorial : ℝ) * ((r - j).factorial : ℝ)) *
              ((d - r).factorial : ℝ)) *
            (((s - i).choose (r - i) : ℝ) * ((r - i).factorial : ℝ) * ((s - r).factorial : ℝ)) := by
            rw [← h5]
      _ = ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) * (j.factorial : ℝ) *
            ((-1 : ℝ) ^ r * ((s - i).choose (r - i) : ℝ) * (r.choose j : ℝ)) * (d.choose r : ℝ) *
            (((r - i).factorial : ℝ) * ((r - j).factorial : ℝ) * ((s - r).factorial : ℝ) *
              (((d - r).factorial : ℝ) * ((d - r).factorial : ℝ))) := by ring
  rw [Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum]
  have hext : (∑ r ∈ Finset.Icc (max i j) s,
      (-1 : ℝ) ^ r * ((s - i).choose (r - i) : ℝ) * (r.choose j : ℝ)) =
      ∑ r ∈ Finset.Icc i s,
        (-1 : ℝ) ^ r * ((s - i).choose (r - i) : ℝ) * (r.choose j : ℝ) := by
    refine Finset.sum_subset (fun r hr => ?_) (fun r hr hnot => ?_)
    · rw [Finset.mem_Icc] at hr ⊢
      exact ⟨le_trans (le_max_left i j) hr.1, hr.2⟩
    · rw [Finset.mem_Icc] at hr hnot
      have hlt : r < j := by omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
  rw [hext]
  have hreidx : (∑ r ∈ Finset.Icc i s,
      (-1 : ℝ) ^ r * ((s - i).choose (r - i) : ℝ) * (r.choose j : ℝ)) =
      ∑ q ∈ Finset.range (s - i + 1),
        (-1 : ℝ) ^ (i + q) * ((s - i).choose q : ℝ) * ((i + q).choose j : ℝ) := by
    refine Finset.sum_bij (fun r _ => r - i) (fun r hr => ?_) (fun r₁ hr₁ r₂ hr₂ h => ?_)
      (fun q hq => ?_) (fun r hr => ?_)
    · rw [Finset.mem_Icc] at hr; rw [Finset.mem_range]; omega
    · rw [Finset.mem_Icc] at hr₁ hr₂; omega
    · rw [Finset.mem_range] at hq
      exact ⟨i + q, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · rw [Finset.mem_Icc] at hr
      have hadd : i + (r - i) = r := by omega
      rw [hadd]
  rw [hreidx]
  have hpoly_id : (∑ q ∈ Finset.range (s - i + 1),
      C ((-1 : ℝ) ^ (i + q) * ((s - i).choose q : ℝ)) * (1 + X : ℝ[X]) ^ (i + q)) =
      C ((-1 : ℝ) ^ s) * (X ^ (s - i) * (1 + X : ℝ[X]) ^ i) := by
    have h1 : (∑ q ∈ Finset.range (s - i + 1),
        C ((-1 : ℝ) ^ (i + q) * ((s - i).choose q : ℝ)) * (1 + X : ℝ[X]) ^ (i + q)) =
        C ((-1 : ℝ) ^ i) * (1 + X : ℝ[X]) ^ i *
          ∑ q ∈ Finset.range (s - i + 1),
            (C (-1 : ℝ) * (1 + X : ℝ[X])) ^ q * (1 : ℝ[X]) ^ (s - i - q) * ((s - i).choose q : ℝ[X]) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hnat : ((s - i).choose q : ℝ[X]) = C ((s - i).choose q : ℝ) := by simp
      rw [hnat, pow_add (-1 : ℝ) i q, pow_add (1 + X : ℝ[X]) i q, one_pow, mul_one,
        mul_pow, ← C_pow, C_mul, C_mul]
      ring
    rw [h1, ← add_pow (C (-1 : ℝ) * (1 + X : ℝ[X])) 1 (s - i)]
    have hsubX : C (-1 : ℝ) * (1 + X : ℝ[X]) + 1 = C (-1 : ℝ) * X := by
      rw [C_neg, C_1]; ring
    rw [hsubX, mul_pow, ← C_pow]
    have hsign_s : (-1 : ℝ) ^ i * (-1 : ℝ) ^ (s - i) = (-1 : ℝ) ^ s := by
      rw [← pow_add, Nat.add_sub_cancel' his]
    calc C ((-1 : ℝ) ^ i) * (1 + X : ℝ[X]) ^ i * (C ((-1 : ℝ) ^ (s - i)) * X ^ (s - i))
        = (C ((-1 : ℝ) ^ i) * C ((-1 : ℝ) ^ (s - i))) * (X ^ (s - i) * (1 + X : ℝ[X]) ^ i) := by ring
      _ = C ((-1 : ℝ) ^ s) * (X ^ (s - i) * (1 + X : ℝ[X]) ^ i) := by rw [← C_mul, hsign_s]
  have hcoeff := congrArg (fun P : ℝ[X] => P.coeff j) hpoly_id
  have hlhs_coeff : (∑ q ∈ Finset.range (s - i + 1),
      C ((-1 : ℝ) ^ (i + q) * ((s - i).choose q : ℝ)) * (1 + X : ℝ[X]) ^ (i + q)).coeff j =
      ∑ q ∈ Finset.range (s - i + 1),
        (-1 : ℝ) ^ (i + q) * ((s - i).choose q : ℝ) * ((i + q).choose j : ℝ) := by
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Polynomial.coeff_C_mul, add_comm (1 : ℝ[X]) X, Polynomial.coeff_X_add_one_pow, mul_assoc]
  rw [← hlhs_coeff, hcoeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hlt : i + j < s
  · have hlt' : ¬(s - i ≤ j) := by omega
    rw [if_neg hlt', if_pos hlt]
    ring
  · rw [if_neg hlt]
    have hge' : s - i ≤ j := by omega
    rw [if_pos hge', add_comm (1 : ℝ[X]) X, Polynomial.coeff_X_add_one_pow]
    by_cases heq : i + j = s
    · rw [if_pos heq]
      have hjsi : j = s - i := by omega
      subst hjsi
      simp only [pref, tsub_self, Nat.choose_zero_right, Nat.cast_one]
      have hsifac_ne : ((s - i).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [div_self hsifac_ne]
      ring
    · rw [if_neg heq]
      dsimp only [pref]
      ring

/-- Rescaled polynomial `t^d p(t⁻¹ (x - 1))` satisfying `(1 + t A).charpoly = (x - (1 + ta)) shiftPoly`. -/
noncomputable def shiftPoly (d : ℕ) (t : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C (t ^ d) * p.comp (C t⁻¹ * (X - 1))

lemma charpoly_one_add_smul_comp {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) :
    ((1 + t • M).charpoly).comp (1 + C t * X) = C (t ^ m) * M.charpoly := by
  let φ : ℝ[X] →+* ℝ[X] := Polynomial.eval₂RingHom C (1 + C t * X)
  have hcomp : ((1 + t • M).charpoly).comp (1 + C t * X) = φ (1 + t • M).charpoly := rfl
  rw [hcomp]
  unfold Matrix.charpoly
  rw [φ.map_det]
  have hmat : φ.mapMatrix (Matrix.charmatrix (1 + t • M)) =
      C t • Matrix.charmatrix M := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, φ, Polynomial.coe_eval₂RingHom]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_one,
        Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C, C_add, C_1, C_mul]
      ring
    · simp only [hij, if_false, zero_add, Polynomial.eval₂_sub, Polynomial.eval₂_zero,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, C_mul]
      ring
  rw [hmat, Matrix.det_smul, Fintype.card_fin, ← C_pow]

lemma charpoly_one_add_smul_factor {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    {c : ℝ} {p : ℝ[X]} (hp : M.charpoly = (X - C c) * p) {t : ℝ} (ht : t ≠ 0) :
    (1 + t • M).charpoly = (X - C (1 + t * c)) * shiftPoly d t p := by
  have h1 := charpoly_one_add_smul_comp M t
  have hcomp_id : (1 + C t * X).comp (C t⁻¹ * (X - 1)) = X := by
    rw [Polynomial.add_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ht, C_1, one_mul]
    ring
  have hlhs := congrArg (fun Q : ℝ[X] => Q.comp (C t⁻¹ * (X - 1))) h1
  rw [Polynomial.comp_assoc, hcomp_id, Polynomial.comp_X] at hlhs
  rw [hlhs, hp, Polynomial.mul_comp, Polynomial.C_comp, pow_succ', C_mul]
  have hlin : C t * (X - C c).comp (C t⁻¹ * (X - 1)) = X - C (1 + t * c) := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, mul_sub, ← mul_assoc,
      ← C_mul, mul_inv_cancel₀ ht, C_1, one_mul, ← C_mul, C_add, C_1]
    ring
  unfold shiftPoly
  rw [Polynomial.mul_comp, mul_mul_mul_comm, hlin]

lemma poly_eq_sum_ffCoeff {d : ℕ} {p : ℝ[X]} (hdeg : p.natDegree ≤ d) :
    p = ∑ i ∈ Finset.range (d + 1), C ((-1 : ℝ) ^ i * ffCoeff d p i) * X ^ (d - i) := by
  ext j
  rw [Polynomial.finsetSum_coeff]
  by_cases hle : j ≤ d
  · rw [Finset.sum_eq_single (d - j)]
    · have hsub : d - (d - j) = j := by omega
      simp only [ffCoeff, hsub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_true, mul_one,
        ← mul_assoc]
      have hsign : (-1 : ℝ) ^ (d - j) * (-1 : ℝ) ^ (d - j) = 1 := by rw [← mul_pow]; norm_num
      rw [hsign, one_mul]
    · intro i hi hne
      have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · have hgt : p.natDegree < j := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

lemma ffCoeff_shiftPoly {d : ℕ} {p : ℝ[X]} (hdeg : p.natDegree ≤ d) {t : ℝ} (ht : t ≠ 0)
    {r : ℕ} (hr : r ≤ d) :
    ffCoeff d (shiftPoly d t p) r =
      ∑ i ∈ Finset.range (r + 1), ((d - i).choose (r - i) : ℝ) * t ^ i * ffCoeff d p i := by
  have hp_exp := poly_eq_sum_ffCoeff hdeg
  have hshift_exp : shiftPoly d t p =
      ∑ i ∈ Finset.range (d + 1), C ((-1 : ℝ) ^ i * t ^ i * ffCoeff d p i) * (X - 1 : ℝ[X]) ^ (d - i) := by
    unfold shiftPoly
    conv_lhs => rw [hp_exp]
    rw [Polynomial.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      mul_pow, ← C_pow]
    have htpow : t ^ d * t⁻¹ ^ (d - i) = t ^ i := by
      calc t ^ d * t⁻¹ ^ (d - i)
          = t ^ (i + (d - i)) * t⁻¹ ^ (d - i) := by rw [Nat.add_sub_cancel' hi']
        _ = t ^ i * (t * t⁻¹) ^ (d - i) := by rw [pow_add, mul_assoc, ← mul_pow]
        _ = t ^ i := by rw [mul_inv_cancel₀ ht, one_pow, mul_one]
    calc C (t ^ d) * (C ((-1 : ℝ) ^ i * ffCoeff d p i) * (C (t⁻¹ ^ (d - i)) * (X - 1) ^ (d - i)))
        = (C (t ^ d) * C (t⁻¹ ^ (d - i)) * C ((-1 : ℝ) ^ i * ffCoeff d p i)) * (X - 1) ^ (d - i) := by
            ring
      _ = C ((-1 : ℝ) ^ i * t ^ i * ffCoeff d p i) * (X - 1) ^ (d - i) := by
            rw [← C_mul, ← C_mul, htpow]
            ring_nf
  unfold ffCoeff
  conv_lhs => rw [hshift_exp]
  rw [Polynomial.finsetSum_coeff, Finset.mul_sum]
  have hsplit : (∑ i ∈ Finset.range (d + 1),
      (-1 : ℝ) ^ r * (C ((-1 : ℝ) ^ i * t ^ i * ffCoeff d p i) * (X - 1 : ℝ[X]) ^ (d - i)).coeff (d - r)) =
      ∑ i ∈ Finset.range (r + 1),
        (-1 : ℝ) ^ r * (C ((-1 : ℝ) ^ i * t ^ i * ffCoeff d p i) * (X - 1 : ℝ[X]) ^ (d - i)).coeff (d - r) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hnot => ?_
    have hir : r < i := by
      rw [Finset.mem_range] at hi hnot; omega
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_C_mul]
    have hdeg_lt : ((X - 1 : ℝ[X]) ^ (d - i)).natDegree < d - r := by
      have hle1 : ((X - 1 : ℝ[X]) ^ (d - i)).natDegree ≤ (d - i) * (X - 1 : ℝ[X]).natDegree :=
        Polynomial.natDegree_pow_le
      have h1 : (X - 1 : ℝ[X]).natDegree = 1 := by
        simpa using Polynomial.natDegree_X_sub_C (1 : ℝ)
      rw [h1, mul_one] at hle1
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg_lt, mul_zero, mul_zero]
  rw [hsplit]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Polynomial.coeff_C_mul]
  have hcoeff_xm1 : ((X - 1 : ℝ[X]) ^ (d - i)).coeff (d - r) =
      (-1 : ℝ) ^ (r - i) * ((d - i).choose (r - i) : ℝ) := by
    have hexp_xm1 : (X - 1 : ℝ[X]) ^ (d - i) =
        ∑ b ∈ Finset.range (d - i + 1),
          C ((-1 : ℝ) ^ (d - i - b) * ((d - i).choose b : ℝ)) * X ^ b := by
      have hsub : (X - 1 : ℝ[X]) = X + C (-1 : ℝ) := by rw [C_neg, C_1, sub_eq_add_neg]
      rw [hsub, add_pow]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hnat : ((d - i).choose b : ℝ[X]) = C ((d - i).choose b : ℝ) := by simp
      rw [← C_pow, hnat, map_mul]
      ring
    rw [hexp_xm1, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (d - r)]
    · have hsub2 : (d - i) - (d - r) = r - i := by omega
      have hchoose_symm : (d - i).choose (d - r) = (d - i).choose (r - i) := by
        rw [← hsub2]
        exact (Nat.choose_symm (by omega : d - r ≤ d - i)).symm
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one, hsub2, hchoose_symm]
    · intro b _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne.symm, mul_zero]
    · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
  rw [hcoeff_xm1]
  have hsign : (-1 : ℝ) ^ r * ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (r - i)) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hir, ← mul_pow]; norm_num
  calc (-1 : ℝ) ^ r * ((-1 : ℝ) ^ i * t ^ i * ffCoeff d p i *
        ((-1 : ℝ) ^ (r - i) * ((d - i).choose (r - i) : ℝ)))
      = ((-1 : ℝ) ^ r * ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (r - i))) *
        (((d - i).choose (r - i) : ℝ) * t ^ i * ffCoeff d p i) := by ring
    _ = ((d - i).choose (r - i) : ℝ) * t ^ i * ffCoeff d p i := by rw [hsign, one_mul]

/-- Limit of the rescaled `ffMul` of `shiftPoly`s as `t → 0` equals `ffAdd`. -/
lemma tendsto_rescaled_ffMul_shiftPoly (d : ℕ) (pA pB : ℝ[X])
    (hdegA : pA.natDegree ≤ d) (hdegB : pB.natDegree ≤ d)
    {tn : ℕ → ℝ} (htn_ne : ∀ n, tn n ≠ 0) (htn_lim : Tendsto tn atTop (nhds 0)) :
    ∀ k, Tendsto
      (fun n => (C ((tn n)⁻¹ ^ d) *
        (ffMul d (shiftPoly d (tn n) pA) (shiftPoly d (tn n) pB)).comp (1 + C (tn n) * X)).coeff k)
      atTop (nhds ((ffAdd d pA pB).coeff k)) := by
  -- Express `C (t⁻¹ ^ d) * (ffMul d (shiftPoly d t pA) (shiftPoly d t pB)).comp (1 + C t * X)` for any `t ≠ 0`
  have hexpand : ∀ {t : ℝ} (ht : t ≠ 0),
      C (t⁻¹ ^ d) * (ffMul d (shiftPoly d t pA) (shiftPoly d t pB)).comp (1 + C t * X) =
        ∑ s ∈ Finset.range (d + 1),
          C (∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1),
              (if i + j < s then 0
               else if i + j = s then
                 (-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
                   ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
                   ffCoeff d pA i * ffCoeff d pB j
               else
                 t ^ (i + j - s) *
                   ((-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
                     ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
                     ((j.factorial : ℝ) / ((s - i).factorial : ℝ)) *
                     (i.choose (j - (s - i)) : ℝ) *
                     ffCoeff d pA i * ffCoeff d pB j))) * X ^ (d - s) := by
    intro t ht
    unfold ffMul
    rw [Polynomial.sum_comp, Finset.mul_sum]
    -- Expand `(1 + C t * X) ^ (d - r)` for each `r ∈ range (d + 1)`
    have hpow_comp : ∀ r ∈ Finset.range (d + 1),
        (X ^ (d - r) : ℝ[X]).comp (1 + C t * X) =
          ∑ s ∈ Finset.Icc r d, C (((d - r).choose (s - r) : ℝ) * t ^ (d - s)) * X ^ (d - s) := by
      intro r hr
      have hrd : r ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [Polynomial.pow_comp, Polynomial.X_comp, add_comm (1 : ℝ[X]) (C t * X), add_pow]
      -- Reindex `u ∈ range (d - r + 1)` via `s = d - u ∈ Icc r d`
      refine Finset.sum_bij (fun u _ => d - u) (fun u hu => ?_) (fun u₁ hu₁ u₂ hu₂ h => ?_)
        (fun s hs => ?_) (fun u hu => ?_)
      · rw [Finset.mem_range] at hu; rw [Finset.mem_Icc]; omega
      · rw [Finset.mem_range] at hu₁ hu₂; omega
      · rw [Finset.mem_Icc] at hs
        exact ⟨d - s, Finset.mem_range.mpr (by omega), by omega⟩
      · rw [Finset.mem_range] at hu
        have hsub1 : d - (d - u) = u := by omega
        have hsub2 : (d - u) - r = (d - r) - u := by omega
        have hsymm : (d - r).choose ((d - r) - u) = (d - r).choose u :=
          Nat.choose_symm (by omega : u ≤ d - r)
        have hnat : ((d - r).choose u : ℝ[X]) = C ((d - r).choose u : ℝ) := by simp
        rw [hsub1, hsub2, hsymm, one_pow, mul_one, mul_pow, ← C_pow, hnat, map_mul]
        ring
    have hstep1 : (∑ i ∈ Finset.range (d + 1),
        C (t⁻¹ ^ d) * (C ((-1 : ℝ) ^ i * ffCoeff d (shiftPoly d t pA) i *
          ffCoeff d (shiftPoly d t pB) i / (d.choose i : ℝ)) * X ^ (d - i)).comp (1 + C t * X)) =
        ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.Icc r d,
          C (t⁻¹ ^ d * ((-1 : ℝ) ^ r * ffCoeff d (shiftPoly d t pA) r *
            ffCoeff d (shiftPoly d t pB) r / (d.choose r : ℝ)) *
            (((d - r).choose (s - r) : ℝ) * t ^ (d - s))) * X ^ (d - s) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Polynomial.mul_comp, Polynomial.C_comp, hpow_comp r hr, ← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← mul_assoc, ← C_mul, ← C_mul]
    rw [hstep1]
    -- Swap `∑_{r=0}^d ∑_{s ∈ Icc r d}` to `∑_{s=0}^d ∑_{r=0}^s`
    have hswap_rs : ∀ (g : ℕ → ℕ → ℝ[X]),
        (∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.Icc r d, g r s) =
          ∑ s ∈ Finset.range (d + 1), ∑ r ∈ Finset.range (s + 1), g r s := by
      intro g
      have h1 : (∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.Icc r d, g r s) =
          ∑ r ∈ Finset.range (d + 1), ∑ s ∈ (Finset.range (d + 1)).filter (r ≤ ·), g r s := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr ?_ (fun _ _ => rfl)
        ext s; simp [Finset.mem_Icc, Finset.mem_range]; omega
      have h2 : (∑ s ∈ Finset.range (d + 1), ∑ r ∈ Finset.range (s + 1), g r s) =
          ∑ s ∈ Finset.range (d + 1), ∑ r ∈ (Finset.range (d + 1)).filter (· ≤ s), g r s := by
        refine Finset.sum_congr rfl fun s hs => Finset.sum_congr ?_ (fun _ _ => rfl)
        have hsd : s ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        ext r; simp [Finset.mem_range]; omega
      rw [h1, h2]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    rw [hswap_rs]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsd : s ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [← Finset.sum_mul, ← map_sum]
    congr 1; congr 1
    -- Expand `ffCoeff d (shiftPoly d t pA) r` and `ffCoeff d (shiftPoly d t pB) r`
    have hr_expand : ∀ r ∈ Finset.range (s + 1),
        t⁻¹ ^ d * ((-1 : ℝ) ^ r * ffCoeff d (shiftPoly d t pA) r *
          ffCoeff d (shiftPoly d t pB) r / (d.choose r : ℝ)) *
          (((d - r).choose (s - r) : ℝ) * t ^ (d - s)) =
        ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
          (t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s)) *
            ((-1 : ℝ) ^ r * ((d - i).choose (r - i) : ℝ) * ((d - j).choose (r - j) : ℝ) *
              ((d - r).choose (s - r) : ℝ) / (d.choose r : ℝ)) *
            ffCoeff d pA i * ffCoeff d pB j := by
      intro r hr
      have hrs : r ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hrd : r ≤ d := le_trans hrs hsd
      rw [ffCoeff_shiftPoly hdegA ht hrd, ffCoeff_shiftPoly hdegB ht hrd]
      have hprod_ij : (∑ i ∈ Finset.range (r + 1), ((d - i).choose (r - i) : ℝ) * t ^ i * ffCoeff d pA i) *
          (∑ j ∈ Finset.range (r + 1), ((d - j).choose (r - j) : ℝ) * t ^ j * ffCoeff d pB j) =
          ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
            (((d - i).choose (r - i) : ℝ) * t ^ i * ffCoeff d pA i) *
              (((d - j).choose (r - j) : ℝ) * t ^ j * ffCoeff d pB j) :=
        Finset.sum_mul_sum _ _ _ _
      have hlhs_assoc : (-1 : ℝ) ^ r *
          (∑ i ∈ Finset.range (r + 1), ((d - i).choose (r - i) : ℝ) * t ^ i * ffCoeff d pA i) *
          (∑ j ∈ Finset.range (r + 1), ((d - j).choose (r - j) : ℝ) * t ^ j * ffCoeff d pB j) =
          (-1 : ℝ) ^ r * ((∑ i ∈ Finset.range (r + 1), ((d - i).choose (r - i) : ℝ) * t ^ i * ffCoeff d pA i) *
            (∑ j ∈ Finset.range (r + 1), ((d - j).choose (r - j) : ℝ) * t ^ j * ffCoeff d pB j)) :=
        mul_assoc _ _ _
      rw [hlhs_assoc, hprod_ij, Finset.mul_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [Finset.sum_congr rfl hr_expand]
    -- Reorder `∑_{r=0}^s ∑_{i=0}^r ∑_{j=0}^r` to `∑_{i=0}^s ∑_{j=0}^s ∑_{r ∈ Icc (max i j) s}`
    let F : ℕ → ℕ → ℕ → ℝ := fun r i j =>
      (t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s)) *
        ((-1 : ℝ) ^ r * ((d - i).choose (r - i) : ℝ) * ((d - j).choose (r - j) : ℝ) *
          ((d - r).choose (s - r) : ℝ) / (d.choose r : ℝ)) *
        ffCoeff d pA i * ffCoeff d pB j
    have htriple : (∑ r ∈ Finset.range (s + 1), ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), F r i j) =
        ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1), ∑ r ∈ Finset.Icc (max i j) s, F r i j := by
      have hL : (∑ r ∈ Finset.range (s + 1), ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), F r i j) =
          ∑ r ∈ Finset.range (s + 1), ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1),
            if max i j ≤ r then F r i j else 0 := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrs : r ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        have hi_sub : (∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1),
            if max i j ≤ r then F r i j else 0) =
            ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
              if max i j ≤ r then F r i j else 0 := by
          symm
          refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni => ?_
          have hir : r < i := by rw [Finset.mem_range] at hni; omega
          refine Finset.sum_eq_zero fun j _ => ?_
          have : ¬max i j ≤ r := by omega
          simp [this]
        rw [hi_sub]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        symm
        rw [← Finset.sum_filter]
        have hfilt : (Finset.range (s + 1)).filter (fun j => max i j ≤ r) = Finset.range (r + 1) := by
          ext j; simp [Finset.mem_range]; omega
        rw [hfilt]
      rw [hL, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_filter]
      have hfilt2 : (Finset.range (s + 1)).filter (fun r => max i j ≤ r) = Finset.Icc (max i j) s := by
        ext r; simp [Finset.mem_range, Finset.mem_Icc]; omega
      rw [hfilt2]
    rw [htriple]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have his : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hjs : j ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpull : (∑ r ∈ Finset.Icc (max i j) s, F r i j) =
        (t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s)) *
          (∑ r ∈ Finset.Icc (max i j) s,
            (-1 : ℝ) ^ r * ((d - i).choose (r - i) : ℝ) * ((d - j).choose (r - j) : ℝ) *
              ((d - r).choose (s - r) : ℝ) / (d.choose r : ℝ)) *
          ffCoeff d pA i * ffCoeff d pB j := by
      simp only [F, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [hpull, alternating_choose_sum_Icc d i j s his hjs hsd]
    split_ifs with hlt heq
    · ring
    · -- `i + j = s`: `t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s) = 1`
      have ht1 : t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s) = 1 := by
        rw [mul_assoc (t⁻¹ ^ d), ← pow_add, heq, mul_assoc, ← pow_add,
          Nat.add_sub_cancel' hsd, ← mul_pow, inv_mul_cancel₀ ht, one_pow]
      rw [ht1]; ring
    · -- `i + j > s`: `t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s) = t ^ (i + j - s)`
      have hgt : s ≤ i + j := by omega
      have ht_pow : t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s) = t ^ (i + j - s) := by
        have hsum_exp : i + j + (d - s) = d + (i + j - s) := by omega
        calc t⁻¹ ^ d * t ^ i * t ^ j * t ^ (d - s)
            = t⁻¹ ^ d * (t ^ i * t ^ j * t ^ (d - s)) := by ring
          _ = t⁻¹ ^ d * t ^ (i + j + (d - s)) := by rw [← pow_add, ← pow_add]
          _ = t⁻¹ ^ d * (t ^ d * t ^ (i + j - s)) := by rw [hsum_exp, pow_add]
          _ = (t⁻¹ * t) ^ d * t ^ (i + j - s) := by rw [← mul_assoc, ← mul_pow]
          _ = t ^ (i + j - s) := by rw [inv_mul_cancel₀ ht, one_pow, one_mul]
      rw [ht_pow]; ring
  -- Now take `n → ∞` (`tn n → 0`) for each coefficient `k`
  intro k
  simp_rw [fun n => hexpand (htn_ne n), Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  unfold ffAdd
  rw [Polynomial.finsetSum_coeff]
  refine tendsto_finsetSum _ fun s hs => ?_
  simp only [Polynomial.coeff_C_mul]
  refine Tendsto.mul ?_ tendsto_const_nhds
  -- At fixed `s`, as `tn n → 0`, only `i + j = s` (`j = s - i`) survives!
  have hlim_ij : Tendsto
      (fun n => ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1),
        if i + j < s then (0 : ℝ)
        else if i + j = s then
          (-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
            ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
            ffCoeff d pA i * ffCoeff d pB j
        else
          tn n ^ (i + j - s) *
            ((-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
              ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
              ((j.factorial : ℝ) / ((s - i).factorial : ℝ)) *
              (i.choose (j - (s - i)) : ℝ) *
              ffCoeff d pA i * ffCoeff d pB j))
      atTop
      (nhds (∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1),
        if i + j = s then
          (-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
            ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
            ffCoeff d pA i * ffCoeff d pB j
        else 0)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    by_cases hlt : i + j < s
    · have hne : i + j ≠ s := by omega
      simp only [if_pos hlt, if_neg hne]
      exact tendsto_const_nhds
    · by_cases heq : i + j = s
      · simp only [if_neg hlt, if_pos heq]
        exact tendsto_const_nhds
      · simp only [if_neg hlt, if_neg heq]
        have hpos : 1 ≤ i + j - s := by omega
        have hp0 : Tendsto (fun n => tn n ^ (i + j - s)) atTop (nhds 0) := by
          simpa [zero_pow (by omega : i + j - s ≠ 0)] using htn_lim.pow (i + j - s)
        simpa using hp0.mul tendsto_const_nhds
  have htarget_eq : (∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1),
      if i + j = s then
        (-1 : ℝ) ^ s * ((d - i).factorial : ℝ) * ((d - j).factorial : ℝ) /
          ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
          ffCoeff d pA i * ffCoeff d pB j
      else 0) =
      (-1 : ℝ) ^ s * ∑ i ∈ Finset.range (s + 1),
        ((d - i).factorial : ℝ) * ((d - (s - i)).factorial : ℝ) /
          ((d.factorial : ℝ) * ((d - s).factorial : ℝ)) *
          ffCoeff d pA i * ffCoeff d pB (s - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have his : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Finset.sum_eq_single (s - i)]
    · have hadd : i + (s - i) = s := Nat.add_sub_cancel' his
      rw [if_pos hadd]
      ring
    · intro j _ hjne
      have hne : i + j ≠ s := by omega
      rw [if_neg hne]
    · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
  rwa [htarget_eq] at hlim_ij

/-- Continuity of `charpoly.coeff k` along `M₀ + t • M₁` as `t → 0`. -/
lemma tendsto_charpoly_add_smul {m : ℕ} (M₀ M₁ : Matrix (Fin m) (Fin m) ℝ)
    {tn : ℕ → ℝ} (htn : Tendsto tn atTop (nhds 0)) (k : ℕ) :
    Tendsto (fun n => ((M₀ + tn n • M₁).charpoly).coeff k) atTop
      (nhds (M₀.charpoly.coeff k)) := by
  have hcont : Continuous (fun t : ℝ => ((M₀ + t • M₁).charpoly).coeff k) := by
    unfold Matrix.charpoly
    have hsignC : ∀ σ : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign σ : ℤ) : ℝ[X]) = C ((Equiv.Perm.sign σ : ℤ) : ℝ) := fun _ => by simp
    simp only [Matrix.det_apply', Polynomial.finsetSum_coeff]
    simp_rw [hsignC, Polynomial.coeff_C_mul]
    refine continuous_finsetSum _ fun σ _ => continuous_const.mul ?_
    have hprod_cont : ∀ S : Finset (Fin m), ∀ j : ℕ,
        Continuous (fun t : ℝ =>
          (∏ i ∈ S, Matrix.charmatrix (M₀ + t • M₁) (σ i) i).coeff j) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro j; simp only [Finset.prod_empty]; exact continuous_const
      | @insert a s ha ih =>
        intro j
        simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
        refine continuous_finsetSum _ fun uv _ => Continuous.mul ?_ (ih uv.2)
        simp only [Matrix.charmatrix, Matrix.sub_apply, Matrix.scalar_apply,
          Matrix.diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, Polynomial.coeff_sub, Polynomial.coeff_C]
        refine continuous_const.sub ?_
        by_cases hu : uv.1 = 0
        · simp only [hu, if_true]
          exact continuous_const.add (continuous_id.mul continuous_const)
        · simp only [if_neg hu]
          exact continuous_const
    exact hprod_cont Finset.univ k
  have h0 := hcont.tendsto 0
  rw [zero_smul, add_zero] at h0
  exact h0.comp htn

/-- Symmetric matrix whose characteristic polynomial has only nonnegative roots is `PosSemidef`. -/
lemma posSemidef_of_symm_roots_nonneg {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.IsSymm) (hroots : ∀ x ∈ M.charpoly.roots, 0 ≤ x) :
    M.PosSemidef := by
  have hMherm : M.IsHermitian := by
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hMherm.posSemidef_iff_eigenvalues_nonneg]
  intro i
  apply hroots
  rw [hMherm.roots_charpoly_eq_eigenvalues]
  exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- `1 + t • A` is `PosSemidef` for positive `t` smaller than `(1 + ∑ |λ_i(A)|)⁻¹`. -/
lemma exists_inv_seq_one_add_smul_posSemidef {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsSymm) :
    ∃ tn : ℕ → ℝ, (∀ n, 0 < tn n) ∧ Tendsto tn atTop (nhds 0) ∧
      ∀ n, (1 + tn n • A).PosSemidef := by
  have hAherm : A.IsHermitian := by
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  let Bnd : ℝ := 1 + ∑ i : Fin m, |hAherm.eigenvalues i|
  have hBnd_pos : 1 ≤ Bnd := by
    have : 0 ≤ ∑ i : Fin m, |hAherm.eigenvalues i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  let tn : ℕ → ℝ := fun n => ((n : ℝ) + Bnd)⁻¹
  have htn_pos : ∀ n, 0 < tn n := fun n => by
    have : (0 : ℝ) < (n : ℝ) + Bnd := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact inv_pos.mpr this
  have htn_lim : Tendsto tn atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop Bnd tendsto_natCast_atTop_atTop)
  refine ⟨tn, htn_pos, htn_lim, fun n => ?_⟩
  have hsymm_n : (1 + tn n • A).IsSymm := by
    ext i j
    simp [Matrix.one_apply, eq_comm, hA.apply i j]
  apply posSemidef_of_symm_roots_nonneg hsymm_n
  intro x hx
  have ht_ne : tn n ≠ 0 := (htn_pos n).ne'
  have heval0 : ((1 + tn n • A).charpoly).eval x = 0 :=
    (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hx
  have hcomp := congrArg (Polynomial.eval ((x - 1) / tn n)) (charpoly_one_add_smul_comp A (tn n))
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_div_cancel₀ _ ht_ne, add_sub_cancel, heval0,
    Polynomial.eval_mul, Polynomial.eval_C] at hcomp
  have hAeval : A.charpoly.eval ((x - 1) / tn n) = 0 :=
    (mul_eq_zero.mp hcomp.symm).resolve_left (pow_ne_zero m ht_ne)
  have hmemA : (x - 1) / tn n ∈ A.charpoly.roots :=
    (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mpr hAeval
  rw [hAherm.roots_charpoly_eq_eigenvalues] at hmemA
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmemA
  have hr_eq : (x - 1) / tn n = hAherm.eigenvalues i := by simpa using hi.symm
  have habs_le : |hAherm.eigenvalues i| ≤ ∑ j : Fin m, |hAherm.eigenvalues j| :=
    Finset.single_le_sum (f := fun j : Fin m => |hAherm.eigenvalues j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hge_neg : -Bnd ≤ hAherm.eigenvalues i := by
    have := neg_abs_le (hAherm.eigenvalues i)
    linarith
  have htn_le : tn n ≤ Bnd⁻¹ := by
    apply inv_anti₀ (by linarith)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hx_eq : x = 1 + tn n * hAherm.eigenvalues i := by
    have := (div_eq_iff ht_ne).mp hr_eq
    linarith
  have hprod_ge : -1 ≤ tn n * hAherm.eigenvalues i := by
    calc -1 = -(Bnd⁻¹ * Bnd) := by rw [inv_mul_cancel₀ (by linarith)]
      _ ≤ -(tn n * Bnd) := by
          have := mul_le_mul_of_nonneg_right htn_le (by linarith : 0 ≤ Bnd)
          linarith
      _ = tn n * (-Bnd) := by ring
      _ ≤ tn n * hAherm.eigenvalues i :=
          mul_le_mul_of_nonneg_left hge_neg (htn_pos n).le
  linarith

/-- Full Lemma 2.5 in dimension `m = d + 1`. -/
theorem lemma_2_5_succ (d : ℕ)
    (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (a b : ℝ) (hA1 : A *ᵥ onesVec (d + 1) = a • onesVec (d + 1))
    (hB1 : B *ᵥ onesVec (d + 1) = b • onesVec (d + 1))
    (pA pB : ℝ[X]) (hpA : A.charpoly = (X - C a) * pA) (hpB : B.charpoly = (X - C b) * pB) :
    expCharpolyAdd A B = (X - C (a + b)) * ffAdd d pA pB ∧
      expCharpolyMul A B = (X - C (a * b)) * ffMul d pA pB ∧
      RealRooted (ffAdd d pA pB) ∧
      ((∀ x ∈ pA.roots, 0 ≤ x) ∨ (∀ x ∈ pB.roots, 0 ≤ x) →
        RealRooted (ffMul d pA pB)) := by
  let m := d + 1
  have hpA_md := monic_and_deg_of_charpoly_factor hpA
  have hpB_md := monic_and_deg_of_charpoly_factor hpB
  -- Part 2: Multiplicative quadrature
  have hmul_quad : expCharpolyMul A B = (X - C (a * b)) * ffMul d pA pB :=
    expCharpolyMul_quadrature d A B hA hB a b hA1 hB1 pA pB hpA hpB
  -- Parts 1 & 3: Additive quadrature and real-rootedness of `ffAdd d pA pB` via `1 + tn n • A`
  obtain ⟨tn, htn_pos, htn_lim, hAt_psd⟩ := exists_inv_seq_one_add_smul_posSemidef A hA
  have htn_ne : ∀ n, tn n ≠ 0 := fun n => (htn_pos n).ne'
  let Qn : ℕ → ℝ[X] := fun n =>
    C ((tn n)⁻¹ ^ m) * (expCharpolyMul (1 + tn n • A) (1 + tn n • B)).comp (1 + C (tn n) * X)
  -- Express `Qn n` on the LHS as `permAvg` of `charpoly (A + P B Pᵀ + tn n • (A P B Pᵀ))`
  have hQn_lhs : ∀ n, Qn n =
      permAvg (fun σ : Equiv.Perm (Fin m) =>
        (A + permMat σ * B * (permMat σ)ᵀ +
          tn n • (A * permMat σ * B * (permMat σ)ᵀ)).charpoly) := by
    intro n
    simp only [Qn, expCharpolyMul, permAvg]
    rw [Polynomial.smul_comp, Algebra.mul_smul_comm, Polynomial.sum_comp, Finset.mul_sum]
    congr 1; congr 1; funext σ
    have hmat_prod : (1 + tn n • A) * permMat σ * (1 + tn n • B) * (permMat σ)ᵀ =
        1 + tn n • (A + permMat σ * B * (permMat σ)ᵀ +
          tn n • (A * permMat σ * B * (permMat σ)ᵀ)) := by
      have hppt : permMat σ * (permMat σ)ᵀ = 1 := by
        have htr : (permMat σ)ᵀ = permMat σ⁻¹ := by
          ext i j; simp [permMat_apply', eq_comm, σ.eq_symm_apply]
        rw [htr, ← permMat_mul_eq, inv_mul_cancel]
        ext i j; simp [permMat_apply', Matrix.one_apply, eq_comm]
      have hL1 : (1 + tn n • A) * permMat σ = permMat σ + tn n • (A * permMat σ) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
      have hL2 : (1 + tn n • B) * (permMat σ)ᵀ = (permMat σ)ᵀ + tn n • (B * (permMat σ)ᵀ) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
      calc (1 + tn n • A) * permMat σ * (1 + tn n • B) * (permMat σ)ᵀ
          = ((1 + tn n • A) * permMat σ) * ((1 + tn n • B) * (permMat σ)ᵀ) := by
              simp only [Matrix.mul_assoc]
        _ = (permMat σ + tn n • (A * permMat σ)) * ((permMat σ)ᵀ + tn n • (B * (permMat σ)ᵀ)) := by
              rw [hL1, hL2]
        _ = permMat σ * (permMat σ)ᵀ +
            tn n • (A * (permMat σ * (permMat σ)ᵀ) + permMat σ * B * (permMat σ)ᵀ +
              tn n • (A * permMat σ * B * (permMat σ)ᵀ)) := by
              rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
              simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_add, smul_smul]
              abel
        _ = 1 + tn n • (A + permMat σ * B * (permMat σ)ᵀ +
            tn n • (A * permMat σ * B * (permMat σ)ᵀ)) := by
              rw [hppt, Matrix.mul_one]
    rw [hmat_prod, charpoly_one_add_smul_comp, ← mul_assoc, ← C_mul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero m (htn_ne n)), C_1, one_mul]
  -- Coefficientwise convergence of `Qn n` to `expCharpolyAdd A B` (LHS)
  have hQn_tend_lhs : ∀ k, Tendsto (fun n => (Qn n).coeff k) atTop
      (nhds ((expCharpolyAdd A B).coeff k)) := by
    intro k
    simp_rw [hQn_lhs]
    unfold expCharpolyAdd permAvg
    simp only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.finsetSum_coeff]
    refine (tendsto_const_nhds.mul ?_)
    refine tendsto_finsetSum _ fun σ _ => ?_
    exact tendsto_charpoly_add_smul (A + permMat σ * B * (permMat σ)ᵀ)
      (A * permMat σ * B * (permMat σ)ᵀ) htn_lim k
  -- Express `Qn n` on the RHS using `expCharpolyMul_quadrature` on `(1 + tn n • A, 1 + tn n • B)`
  have hQn_rhs : ∀ n, Qn n =
      (X - C (a + b + tn n * a * b)) *
        (C ((tn n)⁻¹ ^ d) *
          (ffMul d (shiftPoly d (tn n) pA) (shiftPoly d (tn n) pB)).comp (1 + C (tn n) * X)) := by
    intro n
    have hAsymm_n : (1 + tn n • A).IsSymm := by
      ext i j; simp [Matrix.one_apply, eq_comm, hA.apply i j]
    have hBsymm_n : (1 + tn n • B).IsSymm := by
      ext i j; simp [Matrix.one_apply, eq_comm, hB.apply i j]
    have hA1_n : (1 + tn n • A) *ᵥ onesVec m = (1 + tn n * a) • onesVec m := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hA1, smul_smul, add_smul, one_smul]
    have hB1_n : (1 + tn n • B) *ᵥ onesVec m = (1 + tn n * b) • onesVec m := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hB1, smul_smul, add_smul, one_smul]
    have hpA_n := charpoly_one_add_smul_factor A hpA (htn_ne n)
    have hpB_n := charpoly_one_add_smul_factor B hpB (htn_ne n)
    have hquad_n := expCharpolyMul_quadrature d (1 + tn n • A) (1 + tn n • B)
      hAsymm_n hBsymm_n (1 + tn n * a) (1 + tn n * b) hA1_n hB1_n
      (shiftPoly d (tn n) pA) (shiftPoly d (tn n) pB) hpA_n hpB_n
    dsimp only [Qn]
    rw [hquad_n, Polynomial.mul_comp]
    have hlin_n : C (tn n)⁻¹ *
        (X - C ((1 + tn n * a) * (1 + tn n * b))).comp (1 + C (tn n) * X) =
        X - C (a + b + tn n * a * b) := by
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
      have h1 : C (tn n)⁻¹ * (1 + C (tn n) * X - C ((1 + tn n * a) * (1 + tn n * b))) =
          X - C (tn n)⁻¹ * C (tn n * (a + b + tn n * a * b)) := by
        have hsub : C ((1 + tn n * a) * (1 + tn n * b)) - 1 =
            C (tn n * (a + b + tn n * a * b)) := by
          rw [← C_1, ← C_sub]; congr 1; ring
        have hx : C (tn n)⁻¹ * (C (tn n) * X) = X := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (htn_ne n), C_1, one_mul]
        linear_combination hx - C (tn n)⁻¹ * hsub
      rw [h1, ← C_mul, ← mul_assoc, inv_mul_cancel₀ (htn_ne n), one_mul]
    have hpow_split : C ((tn n)⁻¹ ^ m) = C (tn n)⁻¹ * C ((tn n)⁻¹ ^ d) := by
      rw [← C_mul, pow_succ']
    rw [hpow_split, mul_mul_mul_comm, hlin_n]
  -- Coefficientwise convergence of `Qn n` to `(X - C (a + b)) * ffAdd d pA pB` (RHS)
  have hQn_tend_rhs : ∀ k, Tendsto (fun n => (Qn n).coeff k) atTop
      (nhds (((X - C (a + b)) * ffAdd d pA pB).coeff k)) := by
    intro k
    have hQn_coeff := fun n =>
      (congrArg (fun P : ℝ[X] => P.coeff k) (hQn_rhs n)).trans (Polynomial.coeff_mul _ _ k)
    simp_rw [hQn_coeff]
    rw [Polynomial.coeff_mul]
    refine tendsto_finsetSum _ fun uv _ => ?_
    refine Tendsto.mul ?_ (tendsto_rescaled_ffMul_shiftPoly d pA pB
      hpA_md.2.le hpB_md.2.le htn_ne htn_lim uv.2)
    by_cases hu0 : uv.1 = 0
    · simp only [hu0, Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub]
      have h1 : Tendsto (fun n => a + b + tn n * a * b) atTop (nhds (a + b)) := by
        simpa using tendsto_const_nhds.add ((htn_lim.mul tendsto_const_nhds).mul tendsto_const_nhds)
      exact h1.neg
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C, if_neg hu0, sub_zero]
      exact tendsto_const_nhds
  -- Deduce Part 1 (`expCharpolyAdd` quadrature) by uniqueness of limits!
  have hadd_quad : expCharpolyAdd A B = (X - C (a + b)) * ffAdd d pA pB := by
    ext k
    exact tendsto_nhds_unique (hQn_tend_lhs k) (hQn_tend_rhs k)
  -- Deduce Part 3 (`RealRooted (ffAdd d pA pB)`) via `lemma_2_2` + `tendsto_realRooted`
  have hQn_m_d_rr : ∀ n, (Qn n).Monic ∧ (Qn n).natDegree = m ∧ RealRooted (Qn n) := by
    intro n
    have hAsymm_n : (1 + tn n • A).IsSymm := by
      ext i j; simp [Matrix.one_apply, eq_comm, hA.apply i j]
    have hBsymm_n : (1 + tn n • B).IsSymm := by
      ext i j; simp [Matrix.one_apply, eq_comm, hB.apply i j]
    have hrr_exp := (lemma_2_2 (1 + tn n • A) (1 + tn n • B) hAsymm_n hBsymm_n
      (Or.inl (hAt_psd n))).1
    have hexp_md : (expCharpolyMul (1 + tn n • A) (1 + tn n • B)).Monic ∧
        (expCharpolyMul (1 + tn n • A) (1 + tn n • B)).natDegree = m := by
      let Pexp := expCharpolyMul (1 + tn n • A) (1 + tn n • B)
      have hcard_ne : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by
        rw [Fintype.card_perm, Fintype.card_fin]
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      have hdeg_le : Pexp.natDegree ≤ m := by
        unfold Pexp expCharpolyMul permAvg
        refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      have hcoeff_m : Pexp.coeff m = 1 := by
        unfold Pexp expCharpolyMul permAvg
        rw [Polynomial.coeff_smul, smul_eq_mul, Polynomial.finsetSum_coeff]
        have h1 : ∀ σ : Equiv.Perm (Fin m),
            (((1 + tn n • A) * permMat σ * (1 + tn n • B) * (permMat σ)ᵀ).charpoly).coeff m = 1 := by
          intro σ
          have hm_cp := Matrix.charpoly_monic
            ((1 + tn n • A) * permMat σ * (1 + tn n • B) * (permMat σ)ᵀ)
          have hd_cp : (((1 + tn n • A) * permMat σ * (1 + tn n • B) * (permMat σ)ᵀ).charpoly).natDegree = m := by
            rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
          have hlc := hm_cp.coeff_natDegree
          rwa [hd_cp] at hlc
        rw [Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one, inv_mul_cancel₀ hcard_ne]
      have hdeg_ge : m ≤ Pexp.natDegree := Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff_m]; exact one_ne_zero)
      have hdeg_eq : Pexp.natDegree = m := le_antisymm hdeg_le hdeg_ge
      refine ⟨?_, hdeg_eq⟩
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg_eq, hcoeff_m]
    exact rescale_comp_monic_deg_realRooted hexp_md.1 hexp_md.2 hrr_exp (htn_ne n)
  have hexpAdd_rr : RealRooted (expCharpolyAdd A B) :=
    tendsto_realRooted (fun n => (hQn_m_d_rr n).1) (fun n => (hQn_m_d_rr n).2.1)
      (fun n => (hQn_m_d_rr n).2.2) hQn_tend_lhs
  have hffAdd_rr : RealRooted (ffAdd d pA pB) := by
    rw [hadd_quad] at hexpAdd_rr
    exact (realRooted_of_mul hexpAdd_rr).2
  -- Part 4: Real-rootedness of `ffMul d pA pB` when `pA` or `pB` has nonnegative roots
  have hffMul_rr : ((∀ x ∈ pA.roots, 0 ≤ x) ∨ (∀ x ∈ pB.roots, 0 ≤ x)) →
      RealRooted (ffMul d pA pB) := by
    intro hnonneg
    let A₀ : Matrix (Fin m) (Fin m) ℝ := A - (a / (m : ℝ)) • onesMat m
    let B₀ : Matrix (Fin m) (Fin m) ℝ := B - (b / (m : ℝ)) • onesMat m
    have hm_ne : (m : ℝ) ≠ 0 := by positivity
    have hA₀_symm : A₀.IsSymm := hA.sub ((onesMat_isSymm m).smul _)
    have hB₀_symm : B₀.IsSymm := hB.sub ((onesMat_isSymm m).smul _)
    have hJ_ones : onesMat m *ᵥ onesVec m = (m : ℝ) • onesVec m := by
      ext i; simp [onesMat, Matrix.mulVec, dotProduct, onesVec]
    have hA₀1 : A₀ *ᵥ onesVec m = (0 : ℝ) • onesVec m := by
      change (A - (a / (m : ℝ)) • onesMat m) *ᵥ onesVec m = (0 : ℝ) • onesVec m
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hA1, hJ_ones, smul_smul,
        div_mul_cancel₀ a hm_ne, sub_self, zero_smul]
    have hB₀1 : B₀ *ᵥ onesVec m = (0 : ℝ) • onesVec m := by
      change (B - (b / (m : ℝ)) • onesMat m) *ᵥ onesVec m = (0 : ℝ) • onesVec m
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hB1, hJ_ones, smul_smul,
        div_mul_cancel₀ b hm_ne, sub_self, zero_smul]
    have hA₀J : A₀ * onesMat m = 0 := by
      simpa using mul_onesMat_of_mulVec hA₀1
    have hB₀J : B₀ * onesMat m = 0 := by
      simpa using mul_onesMat_of_mulVec hB₀1
    have hm_cast : (m : ℝ) = (d : ℝ) + 1 := by simp [m]
    have hcpA₀ : A₀.charpoly = (X - C 0) * pA := by
      have hshift := charpoly_add_smul_onesMat d A₀ hA₀J a
      have hadd : A₀ + (a / (d + 1 : ℝ)) • onesMat (d + 1) = A := by
        simpa only [A₀, hm_cast] using sub_add_cancel A ((a / ((d : ℝ) + 1)) • onesMat (d + 1))
      rw [hadd, hpA] at hshift
      have h1 : A₀.charpoly = X * pA := mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero a)
        (calc (X - C a) * A₀.charpoly = X * ((X - C a) * pA) := hshift.symm
          _ = (X - C a) * (X * pA) := by ring)
      simpa using h1
    have hcpB₀ : B₀.charpoly = (X - C 0) * pB := by
      have hshift := charpoly_add_smul_onesMat d B₀ hB₀J b
      have hadd : B₀ + (b / (d + 1 : ℝ)) • onesMat (d + 1) = B := by
        simpa only [B₀, hm_cast] using sub_add_cancel B ((b / ((d : ℝ) + 1)) • onesMat (d + 1))
      rw [hadd, hpB] at hshift
      have h1 : B₀.charpoly = X * pB := mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero b)
        (calc (X - C b) * B₀.charpoly = X * ((X - C b) * pB) := hshift.symm
          _ = (X - C b) * (X * pB) := by ring)
      simpa using h1
    have hquad₀ := expCharpolyMul_quadrature d A₀ B₀ hA₀_symm hB₀_symm 0 0
      hA₀1 hB₀1 pA pB hcpA₀ hcpB₀
    have hpsd₀ : A₀.PosSemidef ∨ B₀.PosSemidef := by
      rcases hnonneg with hpA_nn | hpB_nn
      · left
        apply posSemidef_of_symm_roots_nonneg hA₀_symm
        intro x hx
        rw [hcpA₀, map_zero, sub_zero, Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero hpA_md.1.ne_zero),
          Polynomial.roots_X, Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with rfl | hx'
        · exact le_rfl
        · exact hpA_nn x hx'
      · right
        apply posSemidef_of_symm_roots_nonneg hB₀_symm
        intro x hx
        rw [hcpB₀, map_zero, sub_zero, Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero hpB_md.1.ne_zero),
          Polynomial.roots_X, Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with rfl | hx'
        · exact le_rfl
        · exact hpB_nn x hx'
    have hrr₀ := (lemma_2_2 A₀ B₀ hA₀_symm hB₀_symm hpsd₀).1
    rw [hquad₀] at hrr₀
    exact (realRooted_of_mul hrr₀).2
  exact ⟨hadd_quad, hmul_quad, hffAdd_rr, hffMul_rr⟩

theorem lemma_2_5_main {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (a b : ℝ) (hA1 : A *ᵥ (fun _ => (1 : ℝ)) = a • (fun _ => (1 : ℝ)))
    (hB1 : B *ᵥ (fun _ => (1 : ℝ)) = b • (fun _ => (1 : ℝ)))
    (pA pB : ℝ[X]) (hpA : A.charpoly = (X - C a) * pA) (hpB : B.charpoly = (X - C b) * pB) :
    expCharpolyAdd A B = (X - C (a + b)) * ffAdd (m - 1) pA pB ∧
      expCharpolyMul A B = (X - C (a * b)) * ffMul (m - 1) pA pB ∧
      RealRooted (ffAdd (m - 1) pA pB) ∧
      ((∀ x ∈ pA.roots, 0 ≤ x) ∨ (∀ x ∈ pB.roots, 0 ≤ x) →
        RealRooted (ffMul (m - 1) pA pB)) := by
  cases m with
  | zero =>
    exfalso
    have hdeg0 : A.charpoly.natDegree = 0 := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hne : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
    have hpA_ne : pA ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hpA; exact hne hpA
    rw [hpA, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hpA_ne,
      Polynomial.natDegree_X_sub_C] at hdeg0
    omega
  | succ d =>
    simpa [Nat.add_sub_cancel] using
      lemma_2_5_succ d A B hA hB a b hA1 hB1 pA pB hpA hpB

end MainQuadrature

end SuperRamanujan227.Main

open SuperRamanujan227.Main in
theorem solution {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (a b : ℝ) (hA1 : A *ᵥ (fun _ => (1 : ℝ)) = a • (fun _ => (1 : ℝ)))
    (hB1 : B *ᵥ (fun _ => (1 : ℝ)) = b • (fun _ => (1 : ℝ)))
    (pA pB : ℝ[X]) (hpA : A.charpoly = (X - C a) * pA) (hpB : B.charpoly = (X - C b) * pB) :
    expCharpolyAdd A B = (X - C (a + b)) * ffAdd (m - 1) pA pB ∧
      expCharpolyMul A B = (X - C (a * b)) * ffMul (m - 1) pA pB ∧
      RealRooted (ffAdd (m - 1) pA pB) ∧
      ((∀ x ∈ pA.roots, 0 ≤ x) ∨ (∀ x ∈ pB.roots, 0 ≤ x) →
        RealRooted (ffMul (m - 1) pA pB)) :=
  lemma_2_5_main A B hA hB a b hA1 hB1 pA pB hpA hpB
