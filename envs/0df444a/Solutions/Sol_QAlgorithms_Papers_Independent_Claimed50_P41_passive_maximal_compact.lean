-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.passive_maximal_compact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:17:35.999527+00:00
-- url     : https://prove2.me/submissions/ef6b9848-ea11-4725-b3cc-224d3547298b

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped Matrix.Norms.Frobenius

namespace X4Cayley

open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

noncomputable def cay (A : Matrix m m ℝ) : Matrix m m ℝ := (1 - A) * (1 + A)⁻¹

lemma skew_unit {A : Matrix m m ℝ} (hA : Aᵀ = -A) : IsUnit (1 + A).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 : v ⬝ᵥ ((1 + A) *ᵥ v) = 0 := by rw [h0, dotProduct_zero]
  have h2 : v ⬝ᵥ (A *ᵥ v) = 0 := by
    have e1 : v ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ v) ⬝ᵥ v := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have e2 : (Aᵀ *ᵥ v) ⬝ᵥ v = -(v ⬝ᵥ (A *ᵥ v)) := by
      rw [hA, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, h2, add_zero] at h1
  exact hv (dotProduct_self_eq_zero.mp h1)

lemma comm_inv {X B : Matrix m m ℝ} (hB : IsUnit B.det) (h : X * B = B * X) : X * B⁻¹ = B⁻¹ * X := by
  calc X * B⁻¹ = B⁻¹ * (B * X) * B⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]
    _ = B⁻¹ * (X * B) * B⁻¹ := by rw [h]
    _ = B⁻¹ * X := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]

lemma cay_comm' (A : Matrix m m ℝ) (hA : IsUnit (1 + A).det) : cay A = (1 + A)⁻¹ * (1 - A) := by
  unfold cay
  apply comm_inv hA
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]; abel

lemma one_add_cay {A : Matrix m m ℝ} (hA : IsUnit (1 + A).det) : 1 + cay A = (2 : ℝ) • (1 + A)⁻¹ := by
  unfold cay
  have : (1 : Matrix m m ℝ) = (1 + A) * (1 + A)⁻¹ := (Matrix.mul_nonsing_inv _ hA).symm
  nth_rewrite 1 [this]
  rw [← Matrix.add_mul]
  have : (1 + A + (1 - A)) = (2 : ℝ) • (1 : Matrix m m ℝ) := by
    rw [two_smul]; abel
  rw [this, Matrix.smul_mul, Matrix.one_mul]

lemma one_sub_cay {A : Matrix m m ℝ} (hA : IsUnit (1 + A).det) : 1 - cay A = (2 : ℝ) • (A * (1 + A)⁻¹) := by
  unfold cay
  have : (1 : Matrix m m ℝ) = (1 + A) * (1 + A)⁻¹ := (Matrix.mul_nonsing_inv _ hA).symm
  nth_rewrite 1 [this]
  rw [← Matrix.sub_mul]
  have : (1 + A - (1 - A)) = (2 : ℝ) • A := by
    rw [two_smul]; abel
  rw [this, Matrix.smul_mul]

lemma unit_one_add_cay {A : Matrix m m ℝ} (hA : IsUnit (1 + A).det) : IsUnit (1 + cay A).det := by
  rw [one_add_cay hA, Matrix.det_smul]
  refine IsUnit.mul (by simp) ?_
  rw [Matrix.det_nonsing_inv]; exact hA.ringInverse

lemma cay_cay {A : Matrix m m ℝ} (hA : IsUnit (1 + A).det) : cay (cay A) = A := by
  have hi : ((2 : ℝ) • (1 + A)⁻¹)⁻¹ = (1/2 : ℝ) • (1 + A) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hA]; norm_num
  rw [cay, one_sub_cay hA, one_add_cay hA, hi, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA]
  norm_num


def G (T : Set (Matrix m m ℝ)) : Set (Matrix m m ℝ) := {Q | Qᵀ * Q = 1 ∧ ∀ t ∈ T, Q * t = t * Q}

def W (T : Set (Matrix m m ℝ)) : Submodule ℝ (Matrix m m ℝ) where
  carrier := {A | Aᵀ = -A ∧ ∀ t ∈ T, A * t = t * A}
  add_mem' := by
    rintro A B ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨by rw [Matrix.transpose_add, h1, h3, neg_add], fun t ht => ?_⟩
    rw [Matrix.add_mul, Matrix.mul_add, h2 t ht, h4 t ht]
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨h1, h2⟩
    refine ⟨by rw [Matrix.transpose_smul, h1, smul_neg], fun t ht => ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, h2 t ht]

lemma cay_comm_t {A t : Matrix m m ℝ} (hA : IsUnit (1 + A).det) (h : A * t = t * A) :
    cay A * t = t * cay A := by
  have h1 : t * (1 + A) = (1 + A) * t := by simp [mul_add, add_mul, h]
  have h2 := comm_inv hA h1
  have h3 : (1 - A) * t = t * (1 - A) := by simp [mul_sub, sub_mul, h]
  unfold cay
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

lemma cay_mem_G {T : Set (Matrix m m ℝ)} {A : Matrix m m ℝ} (hA : A ∈ W T) : cay A ∈ G T := by
  obtain ⟨hs, hc⟩ := hA
  have u1 := skew_unit hs
  have u2 : IsUnit (1 - A).det := by
    have := skew_unit (A := -A) (by rw [Matrix.transpose_neg, hs])
    rwa [← sub_eq_add_neg] at this
  refine ⟨?_, fun t ht => cay_comm_t u1 (hc t ht)⟩
  have hT : (cay A)ᵀ = (1 - A)⁻¹ * (1 + A) := by
    rw [cay, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_add,
      Matrix.transpose_sub, Matrix.transpose_one, hs, ← sub_eq_add_neg, sub_neg_eq_add]
  rw [hT, cay]
  have e : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by
    simp only [mul_sub, sub_mul, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]; abel
  calc (1 - A)⁻¹ * (1 + A) * ((1 - A) * (1 + A)⁻¹)
      = (1 - A)⁻¹ * ((1 + A) * (1 - A)) * (1 + A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = ((1 - A)⁻¹ * (1 - A)) * ((1 + A) * (1 + A)⁻¹) := by rw [e]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ u2, Matrix.mul_nonsing_inv _ u1, Matrix.one_mul]

lemma cay_mem_W {T : Set (Matrix m m ℝ)} {Q : Matrix m m ℝ} (hQ : Q ∈ G T) (hu : IsUnit (1 + Q).det) :
    cay Q ∈ W T := by
  obtain ⟨ho, hc⟩ := hQ
  refine ⟨?_, fun t ht => cay_comm_t hu (hc t ht)⟩
  have hP : IsUnit (1 + Qᵀ).det := by
    rw [← Matrix.transpose_one, ← Matrix.transpose_add, Matrix.det_transpose]; exact hu
  have key : (1 + Qᵀ) * (-(cay Q)) = 1 - Qᵀ := by
    have e : (1 + Qᵀ) * (1 - Q) = -((1 - Qᵀ) * (1 + Q)) := by
      simp only [mul_sub, sub_mul, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, ho]; abel
    rw [Matrix.mul_neg, cay, ← Matrix.mul_assoc, e, Matrix.neg_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, neg_neg]
  rw [cay, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_add,
      Matrix.transpose_sub, Matrix.transpose_one, ← key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP,
      Matrix.one_mul, cay]

lemma det_cay {A : Matrix m m ℝ} (hs : Aᵀ = -A) : (cay A).det = 1 := by
  have u1 := skew_unit hs
  have : (1 - A) = (1 + A)ᵀ := by rw [Matrix.transpose_add, Matrix.transpose_one, hs, sub_eq_add_neg]
  rw [cay, Matrix.det_mul, this, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.mul_inverse_cancel _ u1]


open Topology Filter

lemma cay_eq_fun : (cay : Matrix m m ℝ → Matrix m m ℝ) = fun A => (1 - A) * Ring.inverse (1 + A) := by
  funext A; rw [cay, Matrix.nonsing_inv_eq_ringInverse]

lemma cay_contDiffAt {A : Matrix m m ℝ} (hA : IsUnit (1 + A).det) : ContDiffAt ℝ 1 cay A := by
  rw [cay_eq_fun]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hA
  have h1 : ContDiffAt ℝ 1 (fun B : Matrix m m ℝ => Ring.inverse (1 + B)) A := by
    have := contDiffAt_ringInverse ℝ (n := 1) u
    rw [hu] at this
    exact this.comp A (contDiff_const.add contDiff_id).contDiffAt
  exact (contDiff_const.sub contDiff_id).contDiffAt.mul h1

lemma cay_locLip {A : Matrix m m ℝ} (hA : IsUnit (1 + A).det) :
    ∃ K, ∃ t ∈ 𝓝 A, LipschitzOnWith K cay t :=
  (cay_contDiffAt hA).exists_lipschitzOnWith

lemma dimH_le_of_unit {s : Set (Matrix m m ℝ)} (hs : ∀ A ∈ s, IsUnit (1 + A).det) :
    dimH (cay '' s) ≤ dimH s := by
  apply dimH_image_le_of_locally_lipschitzOn
  intro A hA
  obtain ⟨K, t, ht, hK⟩ := cay_locLip (hs A hA)
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

lemma dimH_submodule (V : Submodule ℝ (Matrix m m ℝ)) :
    dimH (V : Set (Matrix m m ℝ)) = Module.finrank ℝ V := by
  have : (V : Set (Matrix m m ℝ)) = ((↑) : V → Matrix m m ℝ) '' Set.univ := by simp
  rw [this, isometry_subtype_coe.dimH_image, Real.dimH_univ_eq_finrank]

lemma G_mul {T : Set (Matrix m m ℝ)} {R Q : Matrix m m ℝ} (hR : R ∈ G T) (hQ : Q ∈ G T) :
    Rᵀ * Q ∈ G T := by
  obtain ⟨h1, h2⟩ := hR
  obtain ⟨h3, h4⟩ := hQ
  have h1' : R * Rᵀ = 1 := mul_eq_one_comm.mp h1
  refine ⟨?_, fun t ht => ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Qᵀ * R * (Rᵀ * Q) = Qᵀ * (R * Rᵀ) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1', Matrix.mul_one, h3]
  · have e : Rᵀ * t = t * Rᵀ := by
      calc Rᵀ * t = Rᵀ * t * (R * Rᵀ) := by rw [h1', Matrix.mul_one]
        _ = Rᵀ * (t * R) * Rᵀ := by simp only [Matrix.mul_assoc]
        _ = Rᵀ * (R * t) * Rᵀ := by rw [h2 t ht]
        _ = t * Rᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h4 t ht, ← Matrix.mul_assoc, e, Matrix.mul_assoc]

theorem dimH_G (T : Set (Matrix m m ℝ)) : dimH (G T) = Module.finrank ℝ (W T) := by
  have : SecondCountableTopology (Matrix m m ℝ) := secondCountable_of_proper
  rw [← dimH_submodule]
  apply le_antisymm
  · -- upper bound via countable dense cover
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (G T)
    have hcov : G T ⊆ ⋃ R : D, (fun X => (R : Matrix m m ℝ) * X) '' (cay '' (W T : Set _)) := by
      intro Q hQ
      let O : Set (G T) := {R | IsUnit (1 + (R : Matrix m m ℝ)ᵀ * Q).det}
      have hO : IsOpen O := by
        have : O = (fun R : G T => (1 + (R : Matrix m m ℝ)ᵀ * Q).det) ⁻¹' {0}ᶜ := by
          ext R; simp [O, isUnit_iff_ne_zero]
        rw [this]
        refine IsOpen.preimage ?_ isOpen_compl_singleton
        fun_prop
      have hQO : (⟨Q, hQ⟩ : G T) ∈ O := by
        simp only [O, Set.mem_ofPred_eq, hQ.1]
        rw [show (1 : Matrix m m ℝ) + 1 = (2 : ℝ) • 1 by rw [two_smul], Matrix.det_smul]; simp
      obtain ⟨R, hRD, hRO⟩ := hDd.exists_mem_open hO ⟨_, hQO⟩
      refine Set.mem_iUnion.mpr ⟨⟨R, hRD⟩, ?_⟩
      have hRQ := G_mul R.2 hQ
      refine ⟨(R : Matrix m m ℝ)ᵀ * Q, ⟨cay ((R : Matrix m m ℝ)ᵀ * Q), cay_mem_W hRQ hRO, cay_cay hRO⟩, ?_⟩
      simp only
      rw [← Matrix.mul_assoc, mul_eq_one_comm.mp R.2.1, Matrix.one_mul]
    have : Countable D := hDc.to_subtype
    calc dimH (G T) ≤ dimH (⋃ R : D, (fun X => (R : Matrix m m ℝ) * X) '' (cay '' (W T : Set _))) :=
          dimH_mono hcov
      _ = ⨆ R : D, dimH ((fun X => (R : Matrix m m ℝ) * X) '' (cay '' (W T : Set _))) := dimH_iUnion _
      _ ≤ dimH (cay '' (W T : Set _)) := by
          refine iSup_le fun R => ?_
          exact (ContinuousLinearMap.mul ℝ (Matrix m m ℝ) (R : Matrix m m ℝ)).lipschitz.dimH_image_le _
      _ ≤ dimH (W T : Set (Matrix m m ℝ)) := dimH_le_of_unit fun A (hA : A ∈ W T) => skew_unit hA.1
  · -- lower bound
    have hsub : cay '' (W T : Set (Matrix m m ℝ)) ⊆ G T := by
      rintro _ ⟨A, hA, rfl⟩; exact cay_mem_G hA
    have hback : cay '' (cay '' (W T : Set (Matrix m m ℝ))) = W T := by
      ext A; constructor
      · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩; rw [cay_cay (skew_unit hB.1)]; exact hB
      · intro hA; exact ⟨cay A, ⟨A, hA, rfl⟩, cay_cay (skew_unit hA.1)⟩
    calc dimH (W T : Set (Matrix m m ℝ)) = dimH (cay '' (cay '' (W T : Set (Matrix m m ℝ)))) := by
          rw [hback]
      _ ≤ dimH (cay '' (W T : Set (Matrix m m ℝ))) := by
          apply dimH_le_of_unit
          rintro _ ⟨A, hA, rfl⟩; exact unit_one_add_cay (skew_unit hA.1)
      _ ≤ dimH (G T) := dimH_mono hsub


theorem dimH_G_det (T : Set (Matrix m m ℝ)) :
    dimH (G T ∩ {Q | Q.det = 1}) = Module.finrank ℝ (W T) := by
  apply le_antisymm
  · rw [← dimH_G]; exact dimH_mono Set.inter_subset_left
  · rw [← dimH_submodule]
    have hsub : cay '' (W T : Set (Matrix m m ℝ)) ⊆ G T ∩ {Q | Q.det = 1} := by
      rintro _ ⟨A, hA, rfl⟩; exact ⟨cay_mem_G hA, det_cay hA.1⟩
    have hback : cay '' (cay '' (W T : Set (Matrix m m ℝ))) = W T := by
      ext A; constructor
      · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩; rw [cay_cay (skew_unit hB.1)]; exact hB
      · intro hA; exact ⟨cay A, ⟨A, hA, rfl⟩, cay_cay (skew_unit hA.1)⟩
    calc dimH (W T : Set (Matrix m m ℝ)) = dimH (cay '' (cay '' (W T : Set (Matrix m m ℝ)))) := by
          rw [hback]
      _ ≤ dimH (cay '' (W T : Set (Matrix m m ℝ))) := by
          apply dimH_le_of_unit
          rintro _ ⟨A, hA, rfl⟩; exact unit_one_add_cay (skew_unit hA.1)
      _ ≤ _ := dimH_mono hsub

/-! ### dimension counts -/

def symSub (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | Aᵀ = A}
  add_mem' := by intro A B h1 h2; simp_all [Matrix.transpose_add]
  zero_mem' := by simp
  smul_mem' := by intro c A h; simp_all [Matrix.transpose_smul]

def symOfLin (n : ℕ) : (Sym2 (Fin n) → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun c := fun i j => c s(i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma symOfLin_apply (n : ℕ) (c : Sym2 (Fin n) → ℝ) (i j : Fin n) :
    symOfLin n c i j = c s(i, j) := rfl

lemma symOfLin_inj (n : ℕ) : Function.Injective (symOfLin n) := by
  intro c d h
  funext z
  induction z using Sym2.ind with
  | _ i j => exact congrFun (congrFun h i) j

lemma range_symOfLin (n : ℕ) : LinearMap.range (symOfLin n) = symSub n := by
  ext B; constructor
  · rintro ⟨c, rfl⟩; ext i j; simp [Matrix.transpose_apply, Sym2.eq_swap]
  · intro hB
    refine ⟨Sym2.lift ⟨fun i j => B i j, fun i j => ?_⟩, ?_⟩
    · exact (congrFun (congrFun hB i) j).symm
    · ext i j; simp

lemma finrank_sym (n : ℕ) : Module.finrank ℝ (symSub n) = n * (n + 1) / 2 := by
  rw [← range_symOfLin, LinearMap.finrank_range_of_inj (symOfLin_inj n),
    Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel, mul_comm]

lemma finrank_skew (n : ℕ) : Module.finrank ℝ (W (∅ : Set (Matrix (Fin n) (Fin n) ℝ))) =
    n * (n - 1) / 2 := by
  have hinf : symSub n ⊓ W ∅ = ⊥ := by
    rw [eq_bot_iff]; rintro A ⟨h1, h2, -⟩
    have : A = -A := h1.symm.trans h2
    simp only [Submodule.mem_bot]
    have h3 : (2 : ℝ) • A = 0 := by rw [two_smul]; nth_rewrite 2 [this]; simp
    exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
  have hsup : symSub n ⊔ W ∅ = ⊤ := by
    rw [eq_top_iff]; intro A _
    have hA : A = (1/2 : ℝ) • (A + Aᵀ) + (1/2 : ℝ) • (A - Aᵀ) := by
      rw [← smul_add]; ext i j; simp; ring
    rw [hA]
    refine Submodule.add_mem_sup ?_ ⟨?_, by simp⟩
    · show _ = _
      rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
    · rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose, ← smul_neg, neg_sub]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (symSub n) (W (∅ : Set (Matrix (Fin n) (Fin n) ℝ)))
  rw [hsup, hinf, finrank_top, finrank_bot, add_zero, finrank_sym, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_fin, mul_one] at h
  have e1 : n * (n + 1) = n * n + n := by ring
  have e2 : n * (n - 1) = n * n - n := Nat.mul_sub_one n n
  rw [e1] at h; rw [e2]
  have : n ≤ n * n := Nat.le_mul_self n
  have hev : (n * n + n) % 2 = 0 := by
    rw [← e1]; exact Nat.even_iff.mp (Nat.even_mul_succ_self n)
  generalize n * n = P at h this hev ⊢
  omega


/-- block form of the passive Lie algebra -/
def blk (n : ℕ) : (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ where
  toFun f := Matrix.fromBlocks f.1 f.2 (-f.2) f.1
  map_add' f g := by simp [Matrix.fromBlocks_add, add_comm]
  map_smul' c f := by simp [Matrix.fromBlocks_smul]

def blk' (n : ℕ) : (W (∅ : Set (Matrix (Fin n) (Fin n) ℝ)) × symSub n) →ₗ[ℝ]
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (blk n).comp ((W ∅).subtype.prodMap (symSub n).subtype)

lemma blk'_apply (n : ℕ) (f : W (∅ : Set (Matrix (Fin n) (Fin n) ℝ)) × symSub n) :
    blk' n f = Matrix.fromBlocks (f.1 : Matrix (Fin n) (Fin n) ℝ) f.2 (-(f.2 : Matrix (Fin n) (Fin n) ℝ)) f.1 := rfl

def sig (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.fromBlocks 0 1 (-1) 0

lemma blk'_inj (n : ℕ) : Function.Injective (blk' n) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ h
  rw [blk'_apply, blk'_apply, Matrix.fromBlocks_inj] at h
  obtain ⟨h1, h2, -, -⟩ := h
  simp only at h1 h2; subst h1; subst h2; rfl

lemma range_blk' (n : ℕ) : LinearMap.range (blk' n) = W {sig n} := by
  ext A; constructor
  · rintro ⟨⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩, rfl⟩
    rw [blk'_apply]
    have hP' : Pᵀ = -P := hP.1
    have hQ' : Qᵀ = Q := hQ
    refine ⟨?_, ?_⟩
    · simp only [Matrix.fromBlocks_transpose, hP', hQ', Matrix.transpose_neg, Matrix.fromBlocks_neg, neg_neg]
    · rintro t rfl
      simp [sig, Matrix.fromBlocks_multiply]
  · rintro ⟨h1, h2⟩
    have h2 := h2 (sig n) rfl
    rw [← Matrix.fromBlocks_toBlocks A] at h1 h2 ⊢
    generalize A.toBlocks₁₁ = P, A.toBlocks₁₂ = Q, A.toBlocks₂₁ = R, A.toBlocks₂₂ = S at h1 h2 ⊢
    simp only [sig, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_inj] at h1 h2
    simp at h2
    obtain ⟨e1, e2, e3, e4⟩ := h2
    obtain ⟨f1, f2, f3, f4⟩ := h1
    subst e4; subst e2
    refine ⟨⟨⟨P, f1, by simp⟩, ⟨Q, ?_⟩⟩, rfl⟩
    show Qᵀ = Q
    rw [f3, neg_neg]

lemma finrank_passive (n : ℕ) : Module.finrank ℝ (W {sig n}) = n ^ 2 := by
  rw [← range_blk', LinearMap.finrank_range_of_inj (blk'_inj n), Module.finrank_prod, finrank_skew,
    finrank_sym]
  have e1 : n * (n + 1) = n * n + n := by ring
  have e2 : n * (n - 1) = n * n - n := Nat.mul_sub_one n n
  have : n ≤ n * n := Nat.le_mul_self n
  have hev : (n * n + n) % 2 = 0 := by
    rw [← e1]; exact Nat.even_iff.mp (Nat.even_mul_succ_self n)
  rw [e1, e2, sq]
  generalize n * n = P at this hev ⊢
  omega

end X4Cayley


open scoped Matrix.Norms.Frobenius
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4GL

open QAlgorithms.Papers.Independent.Claimed50.P41 X4Cayley Matrix Topology

variable {n : ℕ}

lemma dimH_retract {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E →ₗ[ℝ] F) (g : F →ₗ[ℝ] E) (s : Set E) (h : ∀ x ∈ s, g (f x) = x) :
    dimH (f '' s) = dimH s := by
  apply le_antisymm
  · exact (LinearMap.toContinuousLinearMap f).lipschitz.dimH_image_le s
  · have : g '' (f '' s) = s := by
      ext x; constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rw [h y hy]; exact hy
      · intro hx; exact ⟨f x, ⟨x, hx, rfl⟩, h x hx⟩
    calc dimH s = dimH (g '' (f '' s)) := by rw [this]
      _ ≤ dimH (f '' s) := (LinearMap.toContinuousLinearMap g).lipschitz.dimH_image_le _

def diagL (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Phase n) (Phase n) ℝ where
  toFun A := Matrix.fromBlocks A 0 0 A
  map_add' A B := by simp [Matrix.fromBlocks_add]
  map_smul' c A := by simp [Matrix.fromBlocks_smul]

def blk11 (n : ℕ) : Matrix (Phase n) (Phase n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun S := S.toBlocks₁₁
  map_add' A B := by ext; simp [Matrix.toBlocks₁₁]
  map_smul' c A := by ext; simp [Matrix.toBlocks₁₁]

def L1 (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Phase n) (Phase n) ℝ where
  toFun A := Matrix.fromBlocks A 0 0 0
  map_add' A B := by simp [Matrix.fromBlocks_add]
  map_smul' c A := by simp [Matrix.fromBlocks_smul]

def L2 (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Phase n) (Phase n) ℝ where
  toFun A := Matrix.fromBlocks 0 0 0 Aᵀ
  map_add' A B := by simp [Matrix.fromBlocks_add]
  map_smul' c A := by simp [Matrix.fromBlocks_smul]

lemma glMatrix_eq (A : Matrix (Fin n) (Fin n) ℝ) : glMatrix A = L1 n A + L2 n (Ring.inverse A) := by
  show Matrix.fromBlocks A 0 0 A⁻¹ᵀ = Matrix.fromBlocks A 0 0 0 + Matrix.fromBlocks 0 0 0 (Ring.inverse A)ᵀ
  rw [Matrix.fromBlocks_add, Matrix.nonsing_inv_eq_ringInverse]; simp

lemma gl_contDiffAt {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) : ContDiffAt ℝ 1 glMatrix A := by
  have hfun : (glMatrix : Matrix (Fin n) (Fin n) ℝ → _) = fun A => L1 n A + L2 n (Ring.inverse A) := by
    funext A; exact glMatrix_eq A
  rw [hfun]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hA
  have h1 : ContDiffAt ℝ 1 (Ring.inverse : Matrix (Fin n) (Fin n) ℝ → _) A := by
    have := contDiffAt_ringInverse ℝ (n := 1) u
    rwa [hu] at this
  exact (LinearMap.toContinuousLinearMap (L1 n)).contDiff.contDiffAt.add
    ((LinearMap.toContinuousLinearMap (L2 n)).contDiff.contDiffAt.comp A h1)

lemma sigma_eq : sigma n = Matrix.fromBlocks 0 1 (-1) 0 := rfl

lemma part1 (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) : PreservesCanonicalForm (glMatrix A) := by
  unfold PreservesCanonicalForm glMatrix
  rw [sigma_eq, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_transpose, Matrix.transpose_zero]
  simp [Matrix.mul_nonsing_inv _ hA, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hA]

lemma part2 (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    glMatrix (A * B) = glMatrix A * glMatrix B := by
  unfold glMatrix
  rw [Matrix.fromBlocks_multiply, Matrix.mul_inv_rev, Matrix.transpose_mul]
  simp

lemma part3 : Function.Injective (@glMatrix n) := by
  intro A B h
  unfold glMatrix at h
  exact (Matrix.fromBlocks_inj.mp h).1

lemma part4 (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) : (A⁻¹.transpose = A ↔ A.transpose * A = 1) := by
  constructor
  · intro h
    have : A⁻¹ = Aᵀ := by simpa using congrArg Matrix.transpose h
    rw [← this, Matrix.nonsing_inv_mul _ hA]
  · intro h
    rw [Matrix.inv_eq_left_inv h, Matrix.transpose_transpose]

lemma orth_unit {A : Matrix (Fin n) (Fin n) ℝ} (h : A.transpose * A = 1) : IsUnit A.det :=
  Matrix.isUnit_det_of_left_inverse h

lemma gl_orth {A : Matrix (Fin n) (Fin n) ℝ} (h : A.transpose * A = 1) : glMatrix A = Matrix.fromBlocks A 0 0 A := by
  unfold glMatrix; rw [(part4 A (orth_unit h)).mpr h]

lemma part5 (A : Matrix (Fin n) (Fin n) ℝ) (h : A.transpose * A = 1) : IsPassive (Matrix.fromBlocks A 0 0 A) := by
  refine ⟨?_, ?_⟩
  · rw [← gl_orth h]; exact part1 A (orth_unit h)
  · rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]; simp [h]

lemma part6 (hn : 0 < n) :
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, IsUnit A.det ∧ S = glMatrix A} = (n ^ 2 : ℕ) := by
  have hset : {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, IsUnit A.det ∧ S = glMatrix A} =
      glMatrix '' {A | IsUnit A.det} := by
    ext S; simp [eq_comm]
  have hU : dimH {A : Matrix (Fin n) (Fin n) ℝ | IsUnit A.det} = (n ^ 2 : ℕ) := by
    have hopen : IsOpen {A : Matrix (Fin n) (Fin n) ℝ | IsUnit A.det} := by
      have : {A : Matrix (Fin n) (Fin n) ℝ | IsUnit A.det} = (fun A => A.det) ⁻¹' {0}ᶜ := by
        ext A; simp [isUnit_iff_ne_zero]
      rw [this]; exact isOpen_compl_singleton.preimage (by fun_prop)
    rw [Real.dimH_of_mem_nhds (hopen.mem_nhds (x := 1) (by simp)), Module.finrank_matrix,
      Module.finrank_self, Fintype.card_fin, mul_one, sq]
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) := secondCountable_of_proper
  rw [hset]
  apply le_antisymm
  · rw [← hU]
    apply dimH_image_le_of_locally_lipschitzOn
    intro A hA
    obtain ⟨K, t, ht, hK⟩ := (gl_contDiffAt hA).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  · rw [← hU]
    have : blk11 n '' (glMatrix '' {A | IsUnit A.det}) = {A | IsUnit A.det} := by
      ext A; constructor
      · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩; simpa [blk11, glMatrix] using hB
      · intro hA; exact ⟨glMatrix A, ⟨A, hA, rfl⟩, by simp [blk11, glMatrix]⟩
    calc dimH {A : Matrix (Fin n) (Fin n) ℝ | IsUnit A.det}
        = dimH (blk11 n '' (glMatrix '' {A | IsUnit A.det})) := by rw [this]
      _ ≤ _ := (LinearMap.toContinuousLinearMap (blk11 n)).lipschitz.dimH_image_le _

lemma G_empty : G (∅ : Set (Matrix (Fin n) (Fin n) ℝ)) = {A | A.transpose * A = 1} := by
  ext A; simp [G]

lemma part7 :
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ S = glMatrix A} =
      (n * (n - 1) / 2 : ℕ) := by
  have hset : {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ S = glMatrix A} =
      diagL n '' G ∅ := by
    ext S; rw [G_empty]; constructor
    · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, (gl_orth hA).symm⟩
    · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, (gl_orth hA).symm⟩
  rw [hset, dimH_retract (diagL n) (blk11 n) _ (fun x _ => by simp [diagL, blk11]), dimH_G, finrank_skew]

lemma part8 :
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ A.det = 1 ∧ S = glMatrix A} =
      (n * (n - 1) / 2 : ℕ) := by
  have hset : {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ A.det = 1 ∧ S = glMatrix A} =
      diagL n '' (G ∅ ∩ {Q | Q.det = 1}) := by
    ext S; rw [G_empty]; constructor
    · rintro ⟨A, hA, hd, rfl⟩; exact ⟨A, ⟨hA, hd⟩, (gl_orth hA).symm⟩
    · rintro ⟨A, ⟨hA, hd⟩, rfl⟩; exact ⟨A, hA, hd, (gl_orth hA).symm⟩
  rw [hset, dimH_retract (diagL n) (blk11 n) _ (fun x _ => by simp [diagL, blk11]), dimH_G_det, finrank_skew]

end X4GL


open scoped MatrixOrder ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4Polar

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

lemma sigma_transpose : (sigma n).transpose = -sigma n := by
  unfold sigma
  rw [Matrix.fromBlocks_transpose]
  simp [Matrix.fromBlocks_neg]

lemma sigma_mul_sigma : sigma n * sigma n = -1 := by
  unfold sigma
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma sigmaT_mul_sigma : (sigma n).transpose * sigma n = 1 := by
  rw [sigma_transpose, Matrix.neg_mul, sigma_mul_sigma, neg_neg]

lemma sigma_mul_sigmaT : sigma n * (sigma n).transpose = 1 := by
  rw [sigma_transpose, Matrix.mul_neg, sigma_mul_sigma, neg_neg]

lemma symp_mul {X Y : Mat n} (hX : PreservesCanonicalForm X) (hY : PreservesCanonicalForm Y) :
    PreservesCanonicalForm (X * Y) := by
  unfold PreservesCanonicalForm at *
  rw [Matrix.transpose_mul]
  calc X * Y * sigma n * (Y.transpose * X.transpose)
      = X * (Y * sigma n * Y.transpose) * X.transpose := by simp only [Matrix.mul_assoc]
    _ = sigma n := by rw [hY, hX]

lemma symp_isUnit {X : Mat n} (hX : PreservesCanonicalForm X) : IsUnit X.det := by
  have h := congrArg Matrix.det hX
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hs : IsUnit (sigma n).det := by
    have := congrArg Matrix.det (sigma_mul_sigmaT (n := n))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_of_mul_isUnit_left (this ▸ isUnit_one)
  have : IsUnit (X.det * (sigma n).det * X.det) := by rw [h]; exact hs
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this)

lemma symp_transpose {X : Mat n} (hX : PreservesCanonicalForm X) :
    PreservesCanonicalForm X.transpose := by
  unfold PreservesCanonicalForm at *
  rw [Matrix.transpose_transpose]
  have hu := symp_isUnit hX
  -- σ Xᵀ = X⁻¹ σ
  have h1 : sigma n * X.transpose = X⁻¹ * sigma n := by
    calc sigma n * X.transpose = X⁻¹ * (X * sigma n * X.transpose) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = X⁻¹ * sigma n := by rw [hX]
  calc X.transpose * sigma n * X
      = (sigma n).transpose * (sigma n * X.transpose) * sigma n * X := by
        rw [← Matrix.mul_assoc, sigmaT_mul_sigma, Matrix.one_mul]
    _ = (sigma n).transpose * X⁻¹ * (sigma n * sigma n) * X := by
        rw [h1]; simp only [Matrix.mul_assoc]
    _ = sigma n := by
        rw [sigma_mul_sigma, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, sigma_transpose, neg_neg]

lemma symp_inv {X : Mat n} (hX : PreservesCanonicalForm X) :
    PreservesCanonicalForm X⁻¹ := by
  unfold PreservesCanonicalForm at *
  have hu := symp_isUnit hX
  calc X⁻¹ * sigma n * X⁻¹.transpose = X⁻¹ * (X * sigma n * X.transpose) * X⁻¹.transpose := by
        rw [hX]
    _ = sigma n := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu,
          Matrix.transpose_one, Matrix.mul_one]

/-- The positive square root of a positive definite symplectic matrix is symplectic. -/
lemma sqrt_symp {M : Mat n} (hM : M.PosDef) (hMs : PreservesCanonicalForm M) :
    PreservesCanonicalForm (CFC.sqrt M) := by
  set P := CFC.sqrt M with hPdef
  have hP0 : P.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hPP : P * P = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hPu : IsUnit P.det := by
    have := hMu; rw [← hPP, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hMt : M.transpose = M := by
    have := hM.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hPt : P.transpose = P := by
    have := hP0.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- σᵀ M σ = M⁻¹
  have hMinv : (sigma n).transpose * M * sigma n = M⁻¹ := by
    unfold PreservesCanonicalForm at hMs
    rw [hMt] at hMs
    symm
    apply Matrix.inv_eq_left_inv
    calc (sigma n).transpose * M * sigma n * M = (sigma n).transpose * (M * sigma n * M) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMs, sigmaT_mul_sigma]
  have hQ0 : ((sigma n).transpose * P * sigma n).PosSemidef := by
    have := hP0.conjTranspose_mul_mul_same (sigma n)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hQQ : (sigma n).transpose * P * sigma n * ((sigma n).transpose * P * sigma n) = M⁻¹ := by
    rw [← hMinv, ← hPP]
    calc (sigma n).transpose * P * sigma n * ((sigma n).transpose * P * sigma n)
        = (sigma n).transpose * P * (sigma n * (sigma n).transpose) * P * sigma n := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [sigma_mul_sigmaT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hPi0 : P⁻¹.PosSemidef := hP0.inv
  have hPiPi : P⁻¹ * P⁻¹ = M⁻¹ := by
    rw [← hPP, Matrix.mul_inv_rev]
  have hQ : (sigma n).transpose * P * sigma n = P⁻¹ := by
    have h1 := (CFC.sqrt_eq_iff M⁻¹ _ hM.inv.posSemidef.nonneg hQ0.nonneg).mpr hQQ
    have h2 := (CFC.sqrt_eq_iff M⁻¹ _ hM.inv.posSemidef.nonneg hPi0.nonneg).mpr hPiPi
    rw [← h1, h2]
  unfold PreservesCanonicalForm
  rw [hPt]
  have hPs : P * sigma n = sigma n * P⁻¹ := by
    calc P * sigma n = sigma n * ((sigma n).transpose * P * sigma n) := by
          rw [← Matrix.mul_assoc (sigma n), ← Matrix.mul_assoc (sigma n),
            sigma_mul_sigmaT, Matrix.one_mul]
      _ = sigma n * P⁻¹ := by rw [hQ]
  rw [hPs, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one]

lemma transpose_of_posSemidef {M : Mat n} (h : M.PosSemidef) : M.transpose = M := by
  have := h.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma sqrt_facts {M : Mat n} (hM : M.PosDef) (hMs : PreservesCanonicalForm M) :
    IsPositiveSymplectic (CFC.sqrt M) ∧ CFC.sqrt M * CFC.sqrt M = M ∧
      IsUnit (CFC.sqrt M).det := by
  have hPP : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hPu : IsUnit (CFC.sqrt M).det := by
    have := hMu; rw [← hPP, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  refine ⟨⟨sqrt_symp hM hMs, ?_⟩, hPP, hPu⟩
  exact (CFC.sqrt_nonneg M).posSemidef.posDef_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hPu)

lemma polar_KP (S : Mat n) (hS : PreservesCanonicalForm S) :
    ∃! factors : Mat n × Mat n,
      IsPassive factors.1 ∧ IsPositiveSymplectic factors.2 ∧ S = factors.1 * factors.2 := by
  have hSu := symp_isUnit hS
  set M := S.transpose * S with hMdef
  have hM : M.PosDef := by
    have := Matrix.PosDef.conjTranspose_mul_self S (fun x y hxy => by
      have := congrArg (fun z => S⁻¹ *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hSu] using this)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hMs : PreservesCanonicalForm M := symp_mul (symp_transpose hS) hS
  obtain ⟨⟨hPs, hPd⟩, hPP, hPu⟩ := sqrt_facts hM hMs
  set P := CFC.sqrt M with hPdef
  have hPt : P.transpose = P := transpose_of_posSemidef hPd.posSemidef
  refine ⟨(S * P⁻¹, P), ⟨⟨symp_mul hS (symp_inv hPs), ?_⟩, ⟨hPs, hPd⟩, ?_⟩, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hPt]
    calc P⁻¹ * S.transpose * (S * P⁻¹) = P⁻¹ * (P * P) * P⁻¹ := by
          rw [hPP, hMdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hPu]
  · simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu]
  · rintro ⟨K', P'⟩ ⟨⟨-, hK'⟩, ⟨-, hP'⟩, hS'⟩
    have hP't : P'.transpose = P' := transpose_of_posSemidef hP'.posSemidef
    have hP'P' : P' * P' = M := by
      rw [hMdef, hS', Matrix.transpose_mul, hP't]
      calc P' * P' = P' * (K'.transpose * K') * P' := by rw [hK', Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hP'eq : P' = P := by
      rw [hPdef]
      exact ((CFC.sqrt_eq_iff M P' hM.posSemidef.nonneg hP'.posSemidef.nonneg).mpr hP'P').symm
    subst hP'eq
    refine Prod.ext ?_ rfl
    simp only
    rw [hS', Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]

lemma polar_PK (S : Mat n) (hS : PreservesCanonicalForm S) :
    ∃! factors : Mat n × Mat n,
      IsPositiveSymplectic factors.1 ∧ IsPassive factors.2 ∧ S = factors.1 * factors.2 := by
  have hSu := symp_isUnit hS
  set N := S * S.transpose with hNdef
  have hN : N.PosDef := by
    have := Matrix.PosDef.mul_conjTranspose_self S (fun x y hxy => by
      have := congrArg (fun z => z ᵥ* S⁻¹) hxy
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hSu] using this)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hNs : PreservesCanonicalForm N := symp_mul hS (symp_transpose hS)
  obtain ⟨⟨hPs, hPd⟩, hPP, hPu⟩ := sqrt_facts hN hNs
  set P := CFC.sqrt N with hPdef
  have hPt : P.transpose = P := transpose_of_posSemidef hPd.posSemidef
  refine ⟨(P, P⁻¹ * S), ⟨⟨hPs, hPd⟩, ⟨symp_mul (symp_inv hPs) hS, ?_⟩, ?_⟩, ?_⟩
  · apply mul_eq_one_comm.mp
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hPt]
    calc P⁻¹ * S * (S.transpose * P⁻¹) = P⁻¹ * (P * P) * P⁻¹ := by
          rw [hPP, hNdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hPu]
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu]
  · rintro ⟨P', K'⟩ ⟨⟨-, hP'⟩, ⟨-, hK'⟩, hS'⟩
    have hK'' : K' * K'.transpose = 1 := mul_eq_one_comm.mp hK'
    have hP't : P'.transpose = P' := transpose_of_posSemidef hP'.posSemidef
    have hP'P' : P' * P' = N := by
      rw [hNdef, hS', Matrix.transpose_mul, hP't]
      calc P' * P' = P' * (K' * K'.transpose) * P' := by rw [hK'', Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hP'eq : P' = P := by
      rw [hPdef]
      exact ((CFC.sqrt_eq_iff N P' hN.posSemidef.nonneg hP'.posSemidef.nonneg).mpr hP'P').symm
    subst hP'eq
    refine Prod.ext rfl ?_
    simp only
    rw [hS', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]

end X4Polar


open scoped MatrixOrder ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4SF

open Matrix QAlgorithms.Papers.Independent.Claimed50.P41

section Polar
variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

lemma sigma_transpose : (sigma n).transpose = -sigma n := by
  unfold sigma
  rw [Matrix.fromBlocks_transpose]
  simp [Matrix.fromBlocks_neg]

lemma sigma_mul_sigma : sigma n * sigma n = -1 := by
  unfold sigma
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma sigmaT_mul_sigma : (sigma n).transpose * sigma n = 1 := by
  rw [sigma_transpose, Matrix.neg_mul, sigma_mul_sigma, neg_neg]

lemma sigma_mul_sigmaT : sigma n * (sigma n).transpose = 1 := by
  rw [sigma_transpose, Matrix.mul_neg, sigma_mul_sigma, neg_neg]

lemma symp_mul {X Y : Mat n} (hX : PreservesCanonicalForm X) (hY : PreservesCanonicalForm Y) :
    PreservesCanonicalForm (X * Y) := by
  unfold PreservesCanonicalForm at *
  rw [Matrix.transpose_mul]
  calc X * Y * sigma n * (Y.transpose * X.transpose)
      = X * (Y * sigma n * Y.transpose) * X.transpose := by simp only [Matrix.mul_assoc]
    _ = sigma n := by rw [hY, hX]

lemma symp_isUnit {X : Mat n} (hX : PreservesCanonicalForm X) : IsUnit X.det := by
  have h := congrArg Matrix.det hX
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hs : IsUnit (sigma n).det := by
    have := congrArg Matrix.det (sigma_mul_sigmaT (n := n))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_of_mul_isUnit_left (this ▸ isUnit_one)
  have : IsUnit (X.det * (sigma n).det * X.det) := by rw [h]; exact hs
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this)

lemma symp_transpose {X : Mat n} (hX : PreservesCanonicalForm X) :
    PreservesCanonicalForm X.transpose := by
  unfold PreservesCanonicalForm at *
  rw [Matrix.transpose_transpose]
  have hu := symp_isUnit hX
  -- σ Xᵀ = X⁻¹ σ
  have h1 : sigma n * X.transpose = X⁻¹ * sigma n := by
    calc sigma n * X.transpose = X⁻¹ * (X * sigma n * X.transpose) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = X⁻¹ * sigma n := by rw [hX]
  calc X.transpose * sigma n * X
      = (sigma n).transpose * (sigma n * X.transpose) * sigma n * X := by
        rw [← Matrix.mul_assoc, sigmaT_mul_sigma, Matrix.one_mul]
    _ = (sigma n).transpose * X⁻¹ * (sigma n * sigma n) * X := by
        rw [h1]; simp only [Matrix.mul_assoc]
    _ = sigma n := by
        rw [sigma_mul_sigma, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, sigma_transpose, neg_neg]

lemma symp_inv {X : Mat n} (hX : PreservesCanonicalForm X) :
    PreservesCanonicalForm X⁻¹ := by
  unfold PreservesCanonicalForm at *
  have hu := symp_isUnit hX
  calc X⁻¹ * sigma n * X⁻¹.transpose = X⁻¹ * (X * sigma n * X.transpose) * X⁻¹.transpose := by
        rw [hX]
    _ = sigma n := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu,
          Matrix.transpose_one, Matrix.mul_one]

/-- The positive square root of a positive definite symplectic matrix is symplectic. -/
lemma sqrt_symp {M : Mat n} (hM : M.PosDef) (hMs : PreservesCanonicalForm M) :
    PreservesCanonicalForm (CFC.sqrt M) := by
  set P := CFC.sqrt M with hPdef
  have hP0 : P.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hPP : P * P = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hPu : IsUnit P.det := by
    have := hMu; rw [← hPP, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hMt : M.transpose = M := by
    have := hM.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hPt : P.transpose = P := by
    have := hP0.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- σᵀ M σ = M⁻¹
  have hMinv : (sigma n).transpose * M * sigma n = M⁻¹ := by
    unfold PreservesCanonicalForm at hMs
    rw [hMt] at hMs
    symm
    apply Matrix.inv_eq_left_inv
    calc (sigma n).transpose * M * sigma n * M = (sigma n).transpose * (M * sigma n * M) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMs, sigmaT_mul_sigma]
  have hQ0 : ((sigma n).transpose * P * sigma n).PosSemidef := by
    have := hP0.conjTranspose_mul_mul_same (sigma n)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hQQ : (sigma n).transpose * P * sigma n * ((sigma n).transpose * P * sigma n) = M⁻¹ := by
    rw [← hMinv, ← hPP]
    calc (sigma n).transpose * P * sigma n * ((sigma n).transpose * P * sigma n)
        = (sigma n).transpose * P * (sigma n * (sigma n).transpose) * P * sigma n := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [sigma_mul_sigmaT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hPi0 : P⁻¹.PosSemidef := hP0.inv
  have hPiPi : P⁻¹ * P⁻¹ = M⁻¹ := by
    rw [← hPP, Matrix.mul_inv_rev]
  have hQ : (sigma n).transpose * P * sigma n = P⁻¹ := by
    have h1 := (CFC.sqrt_eq_iff M⁻¹ _ hM.inv.posSemidef.nonneg hQ0.nonneg).mpr hQQ
    have h2 := (CFC.sqrt_eq_iff M⁻¹ _ hM.inv.posSemidef.nonneg hPi0.nonneg).mpr hPiPi
    rw [← h1, h2]
  unfold PreservesCanonicalForm
  rw [hPt]
  have hPs : P * sigma n = sigma n * P⁻¹ := by
    calc P * sigma n = sigma n * ((sigma n).transpose * P * sigma n) := by
          rw [← Matrix.mul_assoc (sigma n), ← Matrix.mul_assoc (sigma n),
            sigma_mul_sigmaT, Matrix.one_mul]
      _ = sigma n * P⁻¹ := by rw [hQ]
  rw [hPs, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one]

lemma transpose_of_posSemidef {M : Mat n} (h : M.PosSemidef) : M.transpose = M := by
  have := h.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

end Polar

lemma c_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma star_c : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Complex.conj_ofReal]

lemma omega_def (n : ℕ) : canonicalCoordinateMatrix n =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1) := rfl

lemma omegaH (n : ℕ) : (canonicalCoordinateMatrix n).conjTranspose =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 (-Complex.I • 1) (Complex.I • 1) := by
  rw [omega_def, conjTranspose_smul, star_c, fromBlocks_conjTranspose]
  simp [conjTranspose_smul]

lemma omegaT (n : ℕ) : (canonicalCoordinateMatrix n).transpose =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 (Complex.I • 1) (-Complex.I • 1) := by
  rw [omega_def, transpose_smul, fromBlocks_transpose]
  simp

lemma part1 (n : ℕ) : (canonicalCoordinateMatrix n).conjTranspose * canonicalCoordinateMatrix n = 1 := by
  rw [omegaH, omega_def, smul_mul_smul_comm, c_sq, fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul]
  rw [fromBlocks_smul, ← fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma part2 (n : ℕ) : canonicalCoordinateMatrix n * (canonicalCoordinateMatrix n).conjTranspose = 1 := by
  rw [omegaH, omega_def, smul_mul_smul_comm, c_sq, fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul]
  rw [fromBlocks_smul, ← fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma isigma (n : ℕ) : Complex.I • complexify (sigma n) = Matrix.fromBlocks 0 (Complex.I • 1) (-Complex.I • 1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexify, sigma, Matrix.one_apply] <;> split_ifs <;> simp

lemma csigma (n : ℕ) : complexify (sigma n) = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexify, sigma, Matrix.one_apply] <;> split_ifs <;> simp

lemma part3 (n : ℕ) : canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) *
    (canonicalCoordinateMatrix n).transpose = complexify (sigma n) := by
  rw [isigma, omegaT, omega_def, csigma]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  simp [smul_smul]
  rw [fromBlocks_smul]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma part4 (n : ℕ) : canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) *
    (canonicalCoordinateMatrix n).conjTranspose = sigma3 n := by
  rw [isigma, omegaH, omega_def, sigma3]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  simp [smul_smul]
  rw [fromBlocks_smul]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf


lemma cfb {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    complexify (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

lemma part5 {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    complexForm (Matrix.fromBlocks A B C D) = (1 / 2 : ℂ) • Matrix.fromBlocks
      (complexify (A + D) + Complex.I • complexify (C - B))
      (complexify (A - D) + Complex.I • complexify (B + C))
      (complexify (A - D) - Complex.I • complexify (B + C))
      (complexify (A + D) + Complex.I • complexify (B - C)) := by
  rw [complexForm, omegaH, omega_def, cfb]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  congr 2 <;> ext i j <;> simp [complexify, Matrix.add_apply, Matrix.sub_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring


section New
variable {n : ℕ}

lemma cx_mul {a b c : Type*} [Fintype b] (X : Matrix a b ℝ) (Y : Matrix b c ℝ) :
    complexify (X * Y) = complexify X * complexify Y := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_add {a b : Type*} (X Y : Matrix a b ℝ) : complexify (X + Y) = complexify X + complexify Y := by
  ext i j; simp [complexify]

lemma cx_smul {a b : Type*} (r : ℝ) (X : Matrix a b ℝ) : complexify (r • X) = (r : ℂ) • complexify X := by
  ext i j; simp [complexify]

lemma cx_one : complexify (1 : Mat n) = 1 := by
  ext i j; simp [complexify, Matrix.one_apply]; split_ifs <;> simp

lemma cx_conjTranspose {a b : Type*} (X : Matrix a b ℝ) : (complexify X)ᴴ = complexify Xᵀ := by
  ext i j; simp [complexify]

end New

end X4SF


open scoped Matrix.Norms.Frobenius
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4PM

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

abbrev Mt (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

lemma sig_eq : sigma n = Matrix.fromBlocks 0 1 (-1) 0 := rfl

lemma pm_comm {K : Mt n} (h : IsPassive K) : K * sigma n = sigma n * K := by
  obtain ⟨h1, h2⟩ := h
  unfold PreservesCanonicalForm at h1
  have h3 : K * Kᵀ = 1 := mul_eq_one_comm.mp h2
  calc K * sigma n = K * sigma n * (Kᵀ * K) := by rw [h2, Matrix.mul_one]
    _ = (K * sigma n * Kᵀ) * K := by simp only [Matrix.mul_assoc]
    _ = sigma n * K := by rw [h1]

lemma passive_of_comm {K : Mt n} (h1 : Kᵀ * K = 1) (h2 : K * sigma n = sigma n * K) : IsPassive K := by
  refine ⟨?_, h1⟩
  unfold PreservesCanonicalForm
  rw [h2, Matrix.mul_assoc, mul_eq_one_comm.mp h1, Matrix.mul_one]

lemma passive_iff_symp_comm {S : Mt n} (hS : PreservesCanonicalForm S) :
    IsPassive S ↔ S * sigma n = sigma n * S := by
  refine ⟨pm_comm, fun h => ?_⟩
  have h1 : S * Sᵀ = 1 := by
    unfold PreservesCanonicalForm at hS
    rw [h, Matrix.mul_assoc] at hS
    have := congrArg (fun M => (sigma n)ᵀ * M) hS
    simp only [← Matrix.mul_assoc, X4Polar.sigmaT_mul_sigma, Matrix.one_mul] at this
    exact this
  exact ⟨hS, mul_eq_one_comm.mp h1⟩

lemma comm_iff (K : Mt n) : K * sigma n = sigma n * K ↔ ∃ X Y, K = passiveMatrix X Y := by
  constructor
  · intro h
    rw [← Matrix.fromBlocks_toBlocks K] at h ⊢
    generalize K.toBlocks₁₁ = P, K.toBlocks₁₂ = Q, K.toBlocks₂₁ = R, K.toBlocks₂₂ = S at h ⊢
    simp only [sig_eq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h
    simp at h
    obtain ⟨e1, e2, e3, e4⟩ := h
    subst e4; subst e2
    exact ⟨P, Q, rfl⟩
  · rintro ⟨X, Y, rfl⟩
    simp [passiveMatrix, sig_eq, Matrix.fromBlocks_multiply]

lemma pmTK (X Y : Matrix (Fin n) (Fin n) ℝ) : (passiveMatrix X Y)ᵀ * passiveMatrix X Y =
    Matrix.fromBlocks (Xᵀ * X + Yᵀ * Y) (Xᵀ * Y - Yᵀ * X) (Yᵀ * X - Xᵀ * Y) (Yᵀ * Y + Xᵀ * X) := by
  simp [passiveMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, sub_eq_add_neg]

lemma pm_orth_iff (X Y : Matrix (Fin n) (Fin n) ℝ) : (passiveMatrix X Y)ᵀ * passiveMatrix X Y = 1 ↔
    Xᵀ * X + Yᵀ * Y = 1 ∧ Xᵀ * Y = Yᵀ * X := by
  rw [pmTK, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨h1, h2, -, -⟩; exact ⟨h1, sub_eq_zero.mp h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, by rw [h2, sub_self], by rw [h2, sub_self], by rw [add_comm, h1]⟩

lemma UHU (X Y : Matrix (Fin n) (Fin n) ℝ) : (unitaryParameter X Y)ᴴ * unitaryParameter X Y =
    complexify (Xᵀ * X + Yᵀ * Y) + Complex.I • complexify (Yᵀ * X - Xᵀ * Y) := by
  ext i j
  simp only [unitaryParameter, Matrix.mul_apply, Matrix.conjTranspose_apply, complexify, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [star_sub, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring_nf; rw [Complex.I_sq]; ring

lemma cx_re_im_eq_one (A B : Matrix (Fin n) (Fin n) ℝ) :
    complexify A + Complex.I • complexify B = 1 ↔ A = 1 ∧ B = 0 := by
  constructor
  · intro h
    constructor <;> ext i j <;> have := congrFun (congrFun h i) j <;>
      simp only [complexify, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at this <;>
      split_ifs at this with hij <;> simp_all [Matrix.one_apply]
  · rintro ⟨rfl, rfl⟩
    ext i j; simp [complexify, Matrix.one_apply]; split_ifs <;> simp

lemma unitary_iff (X Y : Matrix (Fin n) (Fin n) ℝ) :
    (unitaryParameter X Y)ᴴ * unitaryParameter X Y = 1 ↔ Xᵀ * X + Yᵀ * Y = 1 ∧ Xᵀ * Y = Yᵀ * X := by
  rw [UHU, cx_re_im_eq_one, sub_eq_zero, eq_comm (a := Yᵀ * X)]

lemma part1b (K : Mt n) : IsPassive K ↔ ∃ X Y : Matrix (Fin n) (Fin n) ℝ,
    (unitaryParameter X Y).conjTranspose * unitaryParameter X Y = 1 ∧ K = passiveMatrix X Y := by
  constructor
  · intro h
    obtain ⟨X, Y, rfl⟩ := (comm_iff K).mp (pm_comm h)
    exact ⟨X, Y, (unitary_iff X Y).mpr ((pm_orth_iff X Y).mp h.2), rfl⟩
  · rintro ⟨X, Y, hU, rfl⟩
    exact passive_of_comm ((pm_orth_iff X Y).mpr ((unitary_iff X Y).mp hU)) ((comm_iff _).mpr ⟨X, Y, rfl⟩)


lemma part2 (X Y : Matrix (Fin n) (Fin n) ℝ) :
    complexForm (passiveMatrix X Y) = Matrix.fromBlocks
      (unitaryParameter X Y) 0 0 (fun i j => star (unitaryParameter X Y i j)) := by
  unfold passiveMatrix
  rw [X4SF.part5, Matrix.fromBlocks_smul]
  congr 1 <;> ext i j <;> simp [unitaryParameter, complexify, Complex.ext_iff] <;> ring_nf <;> simp

lemma det_cf (S : Mt n) : (complexForm S).det = (S.det : ℂ) := by
  unfold complexForm
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (canonicalCoordinateMatrix n).det, mul_assoc,
    ← Matrix.det_mul, X4SF.part2, Matrix.det_one, mul_one]
  exact (RingHom.map_det Complex.ofRealHom S).symm

lemma det_passive {K : Mt n} (h : IsPassive K) : K.det = 1 := by
  obtain ⟨X, Y, -, rfl⟩ := (part1b K).mp h
  have h1 : ((passiveMatrix X Y).det : ℂ) = (Complex.normSq (unitaryParameter X Y).det : ℂ) := by
    have : (fun i j => star (unitaryParameter X Y i j) : Matrix (Fin n) (Fin n) ℂ) =
        ((unitaryParameter X Y)ᴴ)ᵀ := by
      ext i j; simp
    rw [← det_cf, part2, this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj]
  have h2 : 0 ≤ (passiveMatrix X Y).det := by
    have := Complex.ofReal_injective h1; rw [this]; exact Complex.normSq_nonneg _
  have h3 : (passiveMatrix X Y).det ^ 2 = 1 := by
    have := congrArg Matrix.det h.2
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [sq]; exact this
  nlinarith

lemma part1a (K : Mt n) : IsPassive K ↔ PreservesCanonicalForm K ∧ K.transpose * K = 1 ∧ K.det = 1 :=
  ⟨fun h => ⟨h.1, h.2, det_passive h⟩, fun h => ⟨h.1, h.2.1⟩⟩

lemma sub_inl_inr {α : Type*} (P Q R T : Matrix (Fin n) (Fin n) α) :
    (Matrix.fromBlocks P Q R T).submatrix Sum.inl Sum.inr = Q := by ext; rfl
lemma sub_inr_inl {α : Type*} (P Q R T : Matrix (Fin n) (Fin n) α) :
    (Matrix.fromBlocks P Q R T).submatrix Sum.inr Sum.inl = R := by ext; rfl

lemma cx_zero_iff (A B : Matrix (Fin n) (Fin n) ℝ) (c : ℂ) (hc : c = Complex.I ∨ c = -Complex.I) :
    (1 / 2 : ℂ) • (complexify A + c • complexify B) = 0 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro h
    constructor <;> ext i j <;> have := congrFun (congrFun h i) j <;>
      rcases hc with rfl | rfl <;>
      simp [complexify, Complex.ext_iff] at this <;> simp [this]
  · rintro ⟨rfl, rfl⟩; ext; simp [complexify]

lemma part3 (S : Mt n) (hS : PreservesCanonicalForm S) :
    IsPassive S ↔ (complexForm S).submatrix Sum.inl Sum.inr = 0 ∧
        (complexForm S).submatrix Sum.inr Sum.inl = 0 := by
  rw [passive_iff_symp_comm hS, comm_iff]
  rw [← Matrix.fromBlocks_toBlocks S, X4SF.part5, Matrix.fromBlocks_smul, sub_inl_inr, sub_inr_inl]
  generalize S.toBlocks₁₁ = A, S.toBlocks₁₂ = B, S.toBlocks₂₁ = C, S.toBlocks₂₂ = D
  rw [sub_eq_add_neg _ (Complex.I • _), ← neg_smul,
    cx_zero_iff _ _ _ (Or.inl rfl), cx_zero_iff _ _ _ (Or.inr rfl)]
  constructor
  · rintro ⟨X, Y, h⟩
    rw [passiveMatrix, Matrix.fromBlocks_inj] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp
  · rintro ⟨⟨h1, h2⟩, -⟩
    refine ⟨A, B, ?_⟩
    rw [sub_eq_zero] at h1; rw [add_eq_zero_iff_eq_neg'] at h2
    rw [h1.symm, h2] at *
    simp [passiveMatrix]


lemma part4 (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    IsPassive (glMatrix A) ↔ A.transpose * A = 1 := by
  constructor
  · intro h
    have := h.2
    unfold glMatrix at this
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at this
    simpa using this.1
  · intro h
    rw [X4GL.gl_orth h]; exact X4GL.part5 A h

lemma part5 : IsMatrixSubgroup {K : Mt n | IsPassive K} := by
  refine ⟨⟨by simp [PreservesCanonicalForm], by simp⟩, ?_, ?_⟩
  · rintro A ⟨hA1, hA2⟩ B ⟨hB1, hB2⟩
    refine ⟨X4Polar.symp_mul hA1 hB1, ?_⟩
    rw [Matrix.transpose_mul]
    calc Bᵀ * Aᵀ * (A * B) = Bᵀ * (Aᵀ * A) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA2, Matrix.mul_one, hB2]
  · rintro A ⟨hA1, hA2⟩
    show IsPassive A⁻¹
    rw [Matrix.inv_eq_left_inv hA2]
    exact ⟨X4Polar.symp_transpose hA1, by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hA2⟩

lemma passive_closed : IsClosed {K : Mt n | IsPassive K} := by
  have : {K : Mt n | IsPassive K} = {K | K * sigma n * Kᵀ = sigma n} ∩ {K | Kᵀ * K = 1} := rfl
  rw [this]
  apply IsClosed.inter
  · exact isClosed_eq ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_transpose)
      continuous_const
  · exact isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const

lemma entry_le {K : Mt n} (h : Kᵀ * K = 1) (i j : Phase n) : K i j ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 := congrFun (congrFun h j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h1
  have h2 : K i j * K i j ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun x => K x j * K x j) (fun x _ => mul_self_nonneg _) (Finset.mem_univ i)
  constructor <;> nlinarith

lemma part6 : IsCompact {K : Mt n | IsPassive K} := by
  have hbox : IsCompact (Set.univ.pi fun _ : Phase n => Set.univ.pi fun _ : Phase n => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hc : Continuous (Matrix.of : (Phase n → Phase n → ℝ) → Mt n) := continuous_id
  refine IsCompact.of_isClosed_subset (hbox.image hc) passive_closed ?_
  intro K hK
  refine ⟨Matrix.of.symm K, ?_, by simp⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  exact fun i j => entry_le hK.2 i j

lemma part8 : Function.Injective (fun f : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      passiveMatrix f.1 f.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [passiveMatrix, Matrix.fromBlocks_inj] at h
  obtain ⟨rfl, rfl, -, -⟩ := h; rfl

lemma part9 (X Y Xprime Yprime : Matrix (Fin n) (Fin n) ℝ) :
      passiveMatrix X Y * passiveMatrix Xprime Yprime =
        passiveMatrix (X * Xprime - Y * Yprime) (X * Yprime + Y * Xprime) := by
  simp only [passiveMatrix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.mul_neg, Matrix.neg_mul] <;> abel

lemma part10 : dimH {K : Mt n | IsPassive K} = (n ^ 2 : ℕ) := by
  have : {K : Mt n | IsPassive K} = X4Cayley.G {sigma n} := by
    ext K; constructor
    · intro h; exact ⟨h.2, fun t ht => by rw [Set.mem_singleton_iff.mp ht]; exact pm_comm h⟩
    · rintro ⟨h1, h2⟩; exact passive_of_comm h1 (h2 _ rfl)
  rw [this, X4Cayley.dimH_G]
  exact congrArg _ (X4Cayley.finrank_passive n)


lemma compact_bound {H : Set (Mt n)} (hH : IsCompact H) :
    ∃ C, ∀ X ∈ H, ∀ i j, |X i j| ≤ C := by
  have hf : Continuous (fun X : Mt n => ∑ i, ∑ j, |X i j|) := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_id.matrix_elem i j).abs
  obtain ⟨C, hC⟩ := hH.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C, fun X hX i j => ?_⟩
  have h1 := hC X hX
  rw [Real.norm_eq_abs] at h1
  calc abs (X i j) ≤ ∑ j, abs (X i j) :=
        Finset.single_le_sum (f := fun j => abs (X i j)) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, abs (X i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, abs (X i j)) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
    _ ≤ abs (∑ i, ∑ j, abs (X i j)) := le_abs_self _
    _ ≤ C := h1

lemma eig_le_one {Q : Mt n} {C : ℝ} (hb : ∀ k : ℕ, ∀ i j, |(Q ^ k) i j| ≤ C) {v : Phase n → ℝ}
    (hv : v ≠ 0) {l : ℝ} (hl : 0 < l) (hQv : Q *ᵥ v = l • v) : l ≤ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hpow : ∀ k : ℕ, (Q ^ k) *ᵥ v = l ^ k • v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  set B := C * ∑ m, |v m|
  have hbd : ∀ k : ℕ, l ^ k * |v j| ≤ B := by
    intro k
    have h1 := congrFun (hpow k) j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h1
    calc l ^ k * |v j| = |l ^ k * v j| := by rw [abs_mul, abs_of_pos (pow_pos hl k)]
      _ = |∑ m, (Q ^ k) j m * v m| := by rw [h1]
      _ ≤ ∑ m, |(Q ^ k) j m * v m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, C * |v m| := Finset.sum_le_sum fun m _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb k j m) (abs_nonneg _)
      _ = B := by simp only [B, Finset.mul_sum]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B / |v j|) hcon
  have hvj : 0 < |v j| := abs_pos.mpr hj
  have := hbd k
  rw [div_lt_iff₀ hvj] at hk
  linarith

lemma part7 (H : Set (Mt n)) (hH : IsMatrixSubgroup H) (hc : IsCompact H)
    (hsymp : ∀ S ∈ H, PreservesCanonicalForm S) (hsub : {K | IsPassive K} ⊆ H) :
    H = {K | IsPassive K} := by
  refine Set.Subset.antisymm ?_ hsub
  intro S hS
  obtain ⟨⟨P, K⟩, ⟨hP, hK, hSPK⟩, -⟩ := X4Polar.polar_PK S (hsymp S hS)
  simp only at hP hK hSPK
  have hKu : IsUnit K.det := Matrix.isUnit_det_of_left_inverse hK.2
  have hPH : P ∈ H := by
    have : P = S * K⁻¹ := by
      rw [hSPK, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.mul_one]
    rw [this]; exact hH.2.1 _ hS _ (hH.2.2 _ (hsub hK))
  have hpowH : ∀ M ∈ H, ∀ k : ℕ, M ^ k ∈ H := by
    intro M hM k; induction k with
    | zero => simpa using hH.1
    | succ k ih => rw [pow_succ]; exact hH.2.1 _ ih _ hM
  obtain ⟨C, hC⟩ := compact_bound hc
  have hPd : P.PosDef := hP.2
  have hPh := hPd.isHermitian
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPd.det_pos.ne'
  have hev : ∀ j, hPh.eigenvalues j = 1 := by
    intro j
    set v : Phase n → ℝ := ⇑(hPh.eigenvectorBasis j)
    have hPv : P *ᵥ v = hPh.eigenvalues j • v := hPh.mulVec_eigenvectorBasis j
    have hv : v ≠ 0 := by
      intro h
      apply hPh.eigenvectorBasis.orthonormal.ne_zero j
      ext k; simpa using congrFun h k
    have hl : 0 < hPh.eigenvalues j := hPd.eigenvalues_pos j
    have h1 : hPh.eigenvalues j ≤ 1 :=
      eig_le_one (fun k i i' => hC _ (hpowH P hPH k) i i') hv hl hPv
    have hPiv : P⁻¹ *ᵥ v = (hPh.eigenvalues j)⁻¹ • v := by
      have : v = P⁻¹ *ᵥ (P *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mulVec]
      conv_rhs => rw [this, hPv, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
    have h2 : (hPh.eigenvalues j)⁻¹ ≤ 1 :=
      eig_le_one (fun k i i' => hC _ (hpowH _ (hH.2.2 P hPH) k) i i') hv (inv_pos.mpr hl) hPiv
    have := (inv_le_one₀ hl).mp h2
    linarith
  have hP1 : P = 1 := by
    have hspec := hPh.spectral_theorem
    have hd : (diagonal (RCLike.ofReal ∘ hPh.eigenvalues) : Mt n) = 1 := by
      ext a b; simp [diagonal_apply, Matrix.one_apply, hev]
    rw [hd, map_one] at hspec
    exact hspec
  rw [hSPK, hP1, Matrix.one_mul]; exact hK

end X4PM


open MeasureTheory
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Claimed50.P41 X4PM in
theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ K : Matrix (Phase n) (Phase n) ℝ,
      (IsPassive K ↔ PreservesCanonicalForm K ∧ K.transpose * K = 1 ∧ K.det = 1) ∧
      (IsPassive K ↔ ∃ X Y : Matrix (Fin n) (Fin n) ℝ,
        (unitaryParameter X Y).conjTranspose * unitaryParameter X Y = 1 ∧
          K = passiveMatrix X Y)) ∧
    (∀ X Y : Matrix (Fin n) (Fin n) ℝ,
      (unitaryParameter X Y).conjTranspose * unitaryParameter X Y = 1 →
        complexForm (passiveMatrix X Y) = Matrix.fromBlocks
          (unitaryParameter X Y) 0 0 (fun i j => star (unitaryParameter X Y i j))) ∧
    (∀ S : Matrix (Phase n) (Phase n) ℝ, PreservesCanonicalForm S →
      (IsPassive S ↔ (complexForm S).submatrix Sum.inl Sum.inr = 0 ∧
        (complexForm S).submatrix Sum.inr Sum.inl = 0)) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det →
      (IsPassive (glMatrix A) ↔ A.transpose * A = 1)) ∧
    IsMatrixSubgroup {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} ∧
    IsCompact {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} ∧
    (∀ H : Set (Matrix (Phase n) (Phase n) ℝ), IsMatrixSubgroup H → IsCompact H →
      (∀ S ∈ H, PreservesCanonicalForm S) → {K | IsPassive K} ⊆ H → H = {K | IsPassive K}) ∧
    Function.Injective (fun f : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      passiveMatrix f.1 f.2) ∧
    (∀ X Y Xprime Yprime : Matrix (Fin n) (Fin n) ℝ,
      passiveMatrix X Y * passiveMatrix Xprime Yprime =
        passiveMatrix (X * Xprime - Y * Yprime) (X * Yprime + Y * Xprime)) ∧
    dimH {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} = (n ^ 2 : ℕ) := ⟨fun K => ⟨part1a K, part1b K⟩, fun X Y _ => part2 X Y, fun S hS => part3 S hS, part4, part5, part6,
    part7, part8, part9, part10⟩
