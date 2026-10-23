-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.williamson_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:34:56.57624+00:00
-- url     : https://prove2.me/submissions/e5aaae26-045e-4565-9da8-a12f974a8199

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


-- ===== PDAbs

open scoped InnerProductSpace RealInnerProductSpace
open Module

namespace X4PD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_eig_in {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {S : Submodule ℝ E}
    (hS : ∀ x ∈ S, T x ∈ S) (hne : S ≠ ⊥) :
    ∃ v ∈ S, v ≠ 0 ∧ ∃ μ : ℝ, T v = μ • v := by
  let T' : S →ₗ[ℝ] S := T.restrict (fun x hx => hS x hx)
  have hT' : T'.IsSymmetric := hT.restrict_invariant (fun x hx => hS x hx)
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨v, hv⟩ := (hT'.hasEigenvalue_iSup_of_finiteDimensional).exists_hasEigenvector
  exact ⟨v, v.2, fun h => hv.2 (Subtype.ext h), _, congrArg Subtype.val hv.apply_eq_smul⟩

/-- The paired family `f i, J (f i)`. -/
def fam (J : E →ₗ[ℝ] E) {k : ℕ} (f : Fin k → E) : Fin k ⊕ Fin k → E :=
  Sum.elim f (fun i => J (f i))

def Good (T J : E →ₗ[ℝ] E) {k : ℕ} (f : Fin k → E) : Prop :=
  Orthonormal ℝ (fam J f) ∧ ∀ x, ∃ μ : ℝ, T (fam J f x) = μ • fam J f x

variable {T J : E →ₗ[ℝ] E}

lemma J_skew (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hJJ : ∀ x, J (J x) = -x) (x y : E) :
    ⟪J x, y⟫ = -⟪x, J y⟫ := by
  have := hJ (J x) y
  rw [hJJ, inner_neg_left] at this
  linarith

lemma step (hT : T.IsSymmetric) (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hJJ : ∀ x, J (J x) = -x)
    (hc : ∀ x, T (J (T (J x))) = J (T (J (T x)))) {k : ℕ} (hk : 2 * k < finrank ℝ E)
    (f : Fin k → E) (hf : Good T J f) :
    ∃ w : E, Good T J (fun i : Fin (k + 1) => if h : (i : ℕ) < k then f ⟨i, h⟩ else w) := by
  set G := Submodule.span ℝ (Set.range (fam J f)) with hGdef
  set S := Gᗮ with hSdef
  have hmemG : ∀ a, fam J f a ∈ G := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hGT : ∀ x ∈ G, T x ∈ G := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨μ, hμ⟩ := hf.2 i
      rw [hμ]; exact G.smul_mem _ (hmemG i)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact G.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact G.smul_mem c ha
  have hGJ : ∀ x ∈ G, J x ∈ G := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rcases i with i | i
      · exact hmemG (Sum.inr i)
      · simp only [fam, Sum.elim_inr]
        rw [hJJ]; exact G.neg_mem (hmemG (Sum.inl i))
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact G.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact G.smul_mem c ha
  have hST : ∀ x ∈ S, T x ∈ S := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro u hu
    rw [← hT]; exact hx _ (hGT u hu)
  have hSJ : ∀ x ∈ S, J x ∈ S := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro u hu
    have := J_skew hJ hJJ u x
    rw [hx _ (hGJ u hu)] at this
    linarith
  have hSne : S ≠ ⊥ := by
    intro h
    have h1 := Submodule.finrank_add_finrank_orthogonal G
    rw [← hSdef, h, finrank_bot] at h1
    have h2 : finrank ℝ G ≤ 2 * k := by
      have := finrank_range_le_card (R := ℝ) (fam J f)
      rw [Set.finrank, ← hGdef] at this
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    omega
  obtain ⟨v, hvS, hv0, lam, hv⟩ := exists_eig_in hT hST hSne
  set S' := S ⊓ Module.End.eigenspace T lam with hS'def
  set W : E →ₗ[ℝ] E := J ∘ₗ T ∘ₗ J with hWdef
  have hW : W.IsSymmetric := by
    intro x y
    simp only [W, LinearMap.comp_apply]
    rw [J_skew hJ hJJ, hT, J_skew hJ hJJ x, neg_neg]
  have hS'W : ∀ x ∈ S', W x ∈ S' := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    rw [Module.End.mem_eigenspace_iff] at hx2
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact hSJ _ (hST _ (hSJ _ hx1))
    · rw [Module.End.mem_eigenspace_iff]
      simp only [W, LinearMap.comp_apply]
      rw [hc, hx2, map_smul, map_smul, map_smul]
  have hS'ne : S' ≠ ⊥ := by
    intro h
    have : v ∈ S' := Submodule.mem_inf.mpr ⟨hvS, Module.End.mem_eigenspace_iff.mpr hv⟩
    rw [h, Submodule.mem_bot] at this
    exact hv0 this
  obtain ⟨w', hw'S, hw'0, mu, hw'⟩ := exists_eig_in hW hS'W hS'ne
  obtain ⟨w, hwdef⟩ : ∃ w, w = ‖w'‖⁻¹ • w' := ⟨_, rfl⟩
  have hwS' : w ∈ S' := hwdef ▸ S'.smul_mem _ hw'S
  have hwS : w ∈ S := (Submodule.mem_inf.mp hwS').1
  have hTw : T w = lam • w := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hwS').2
  have hWw : J (T (J w)) = mu • w := by
    have : W w = mu • w := by rw [hwdef, map_smul, hw', smul_comm]
    exact this
  have hTJw : T (J w) = (-mu) • J w := by
    have := congrArg J hWw
    rw [hJJ, map_smul] at this
    rw [neg_smul, ← this, neg_neg]
  have hJwS : J w ∈ S := hSJ _ hwS
  have hnw : ⟪w, w⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hwdef, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw'0)]
    norm_num
  have hnJw : ⟪J w, J w⟫ = 1 := by rw [hJ, hnw]
  have hwJw : ⟪w, J w⟫ = 0 := by
    have := J_skew hJ hJJ w w
    rw [real_inner_comm] at this
    linarith
  have hJww : ⟪J w, w⟫ = 0 := by rw [real_inner_comm]; exact hwJw
  have horth : ∀ a, ∀ x ∈ S, ⟪fam J f a, x⟫ = 0 := fun a x hx =>
    (Submodule.mem_orthogonal G x).mp hx _ (hmemG a)
  have horth' : ∀ a, ∀ x ∈ S, ⟪x, fam J f a⟫ = 0 := fun a x hx => by
    rw [real_inner_comm]; exact horth a x hx
  have hold := orthonormal_iff_ite.mp hf.1
  refine ⟨w, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    rintro (i | i) (j | j) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq, if_false] <;>
      by_cases hi : (i : ℕ) < k <;> by_cases hj : (j : ℕ) < k <;>
      simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true]
    · have := hold (Sum.inl ⟨i, hi⟩) (Sum.inl ⟨j, hj⟩)
      simp only [fam, Sum.elim_inl, Sum.inl.injEq, Fin.mk.injEq] at this
      rw [this]; simp only [Fin.ext_iff]
    · rw [if_neg (by intro h; rw [Fin.ext_iff] at h; omega)]
      exact horth (Sum.inl ⟨i, hi⟩) w hwS
    · rw [if_neg (by intro h; rw [Fin.ext_iff] at h; omega)]
      exact horth' (Sum.inl ⟨j, hj⟩) w hwS
    · rw [if_pos (by rw [Fin.ext_iff]; omega)]; exact hnw
    · exact hold (Sum.inl ⟨i, hi⟩) (Sum.inr ⟨j, hj⟩)
    · exact horth (Sum.inl ⟨i, hi⟩) _ hJwS
    · exact horth' (Sum.inr ⟨j, hj⟩) w hwS
    · exact hwJw
    · exact hold (Sum.inr ⟨i, hi⟩) (Sum.inl ⟨j, hj⟩)
    · exact horth (Sum.inr ⟨i, hi⟩) _ hwS
    · exact horth' (Sum.inl ⟨j, hj⟩) _ hJwS
    · exact hJww
    · have := hold (Sum.inr ⟨i, hi⟩) (Sum.inr ⟨j, hj⟩)
      simp only [fam, Sum.elim_inr, Sum.inr.injEq, Fin.mk.injEq] at this
      rw [this]; simp only [Fin.ext_iff]
    · rw [if_neg (by intro h; rw [Fin.ext_iff] at h; omega)]
      exact horth (Sum.inr ⟨i, hi⟩) _ hJwS
    · rw [if_neg (by intro h; rw [Fin.ext_iff] at h; omega)]
      exact horth' (Sum.inr ⟨j, hj⟩) _ hJwS
    · rw [if_pos (by rw [Fin.ext_iff]; omega)]; exact hnJw
  · rintro (i | i) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr] <;>
      by_cases hi : (i : ℕ) < k <;> simp only [hi, dif_pos, dif_neg, not_false_eq_true]
    · exact hf.2 (Sum.inl ⟨i, hi⟩)
    · exact ⟨lam, hTw⟩
    · exact hf.2 (Sum.inr ⟨i, hi⟩)
    · exact ⟨-mu, hTJw⟩

lemma build (hT : T.IsSymmetric) (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hJJ : ∀ x, J (J x) = -x)
    (hc : ∀ x, T (J (T (J x))) = J (T (J (T x)))) (n : ℕ) (hE : finrank ℝ E = 2 * n) :
    ∀ k ≤ n, ∃ f : Fin k → E, Good T J f
  | 0, _ => ⟨Fin.elim0, by
      refine ⟨⟨fun i => ?_, fun i => ?_⟩, fun i => ?_⟩ <;> rcases i with i | i <;> exact i.elim0⟩
  | k + 1, hk => by
      obtain ⟨f, hf⟩ := build hT hJ hJJ hc n hE k (by omega)
      obtain ⟨w, hw⟩ := step hT hJ hJJ hc (by omega) f hf
      exact ⟨_, hw⟩

end X4PD


-- ===== PDMat

open scoped InnerProductSpace RealInnerProductSpace
open Module
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4PD

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

abbrev Mq (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

lemma cf_mul (S T : Mq n) : complexForm (S * T) = complexForm S * complexForm T := by
  unfold complexForm
  set O := canonicalCoordinateMatrix n
  have h1 : Oᴴ * O = 1 := X4SF.part1 n
  calc O * complexify (S * T) * Oᴴ = O * complexify S * (Oᴴ * O) * complexify T * Oᴴ := by
        rw [h1, Matrix.mul_one, X4SF.cx_mul]; simp only [Matrix.mul_assoc]
    _ = O * complexify S * Oᴴ * (O * complexify T * Oᴴ) := by simp only [Matrix.mul_assoc]

lemma cfH' (S : Mq n) : (complexForm S)ᴴ = complexForm Sᵀ := by
  unfold complexForm
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, X4SF.cx_conjTranspose,
    Matrix.mul_assoc]

lemma cf_inj {S T : Mq n} (h : complexForm S = complexForm T) : S = T := by
  have key : ∀ X : Mq n, (canonicalCoordinateMatrix n)ᴴ * complexForm X *
      canonicalCoordinateMatrix n = complexify X := by
    intro X
    unfold complexForm
    simp only [← Matrix.mul_assoc, X4SF.part1, Matrix.one_mul]
    rw [Matrix.mul_assoc, X4SF.part1, Matrix.mul_one]
  have := key S
  rw [h, key T] at this
  ext a b
  have := congrFun (congrFun this a) b
  simp only [complexify, Complex.ofReal_inj] at this
  exact this.symm

lemma cf_sigma : complexForm (sigma n) = (-Complex.I) • sigma3 n := by
  rw [← X4SF.part4]
  unfold complexForm
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  simp

lemma s3_conj (M : Matrix (Phase n) (Phase n) ℂ) (a b : Phase n) :
    (sigma3 n * M * sigma3 n) a b =
      (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) a) * (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) b) *
        M a b := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [sigma3, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

lemma cf_entries' (P : Mq n) (hP : Pᵀ = P) (i j : Fin n) :
    complexForm P (Sum.inl j) (Sum.inl i) = complexForm P (Sum.inr i) (Sum.inr j) ∧
    complexForm P (Sum.inl j) (Sum.inr i) = complexForm P (Sum.inl i) (Sum.inr j) := by
  have hs : ∀ a b, P a b = P b a := fun a b => by rw [← transpose_apply P a b, hP]
  rw [← fromBlocks_toBlocks P, X4SF.part5]
  simp [Matrix.smul_apply, complexify, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]
  refine ⟨?_, ?_⟩
  · rw [hs (Sum.inl j) (Sum.inl i), hs (Sum.inr j) (Sum.inr i), hs (Sum.inr j) (Sum.inl i),
      hs (Sum.inl j) (Sum.inr i)]
  · rw [hs (Sum.inl j) (Sum.inl i), hs (Sum.inr j) (Sum.inr i), hs (Sum.inl j) (Sum.inr i),
      hs (Sum.inr j) (Sum.inl i)]; ring

lemma comm_of_symm (V : Mq n) (hV : Vᵀ = V) (h : (noiseA V * noiseB V).IsSymm) :
    V * (sigma n * V * sigma n) = (sigma n * V * sigma n) * V := by
  apply cf_inj
  simp only [cf_mul, cf_sigma, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  set C := complexForm V with hC
  have hH : ∀ a b, C a b = star (C b a) := by
    intro a b
    have : Cᴴ = C := by rw [hC, cfH', hV]
    conv_lhs => rw [← this]
    exact conjTranspose_apply C b a
  have hAB : ∀ i j, ∑ k, C (Sum.inl i) (Sum.inl k) * C (Sum.inl k) (Sum.inr j) =
      ∑ k, C (Sum.inl j) (Sum.inl k) * C (Sum.inl k) (Sum.inr i) := by
    intro i j
    have := congrFun (congrFun h.eq i) j
    simp only [noiseA, noiseB, Matrix.transpose_apply, Matrix.mul_apply, submatrix_apply] at this
    exact this.symm
  have e1 : ∀ j k, C (Sum.inr k) (Sum.inr j) = C (Sum.inl j) (Sum.inl k) := fun j k =>
    ((cf_entries' V hV k j).1).symm
  have e2 : ∀ i k, C (Sum.inl i) (Sum.inr k) = C (Sum.inl k) (Sum.inr i) := fun i k =>
    ((cf_entries' V hV i k).2).symm
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [s3_conj]
  try simp only [Fintype.sum_sum_type]
  rcases a with i | i <;> rcases b with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · ring_nf
  · -- (inl i, inr j)
    have key : ∑ k, C (Sum.inl i) (Sum.inr k) * C (Sum.inr k) (Sum.inr j) =
        ∑ k, C (Sum.inl i) (Sum.inl k) * C (Sum.inl k) (Sum.inr j) := by
      rw [hAB i j]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e1 j k, e2 i k, mul_comm]
    simp only [neg_mul, one_mul, mul_neg, neg_neg, mul_one, Finset.sum_neg_distrib]
    rw [key]; ring
  · -- (inr i, inl j)
    have keyX : ∑ k, C (Sum.inr i) (Sum.inl k) * C (Sum.inl k) (Sum.inl j) =
        star (∑ k, C (Sum.inl j) (Sum.inl k) * C (Sum.inl k) (Sum.inr i)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hH (Sum.inr i) (Sum.inl k), hH (Sum.inl k) (Sum.inl j), star_mul', mul_comm]
    have keyY : ∑ k, C (Sum.inr i) (Sum.inr k) * C (Sum.inr k) (Sum.inl j) =
        star (∑ k, C (Sum.inl i) (Sum.inl k) * C (Sum.inl k) (Sum.inr j)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e1 k i, hH (Sum.inl k) (Sum.inl i), hH (Sum.inr k) (Sum.inl j), e2 j k, star_mul']
    simp only [neg_mul, one_mul, mul_neg, neg_neg, mul_one, Finset.sum_neg_distrib]
    rw [keyX, keyY, hAB i j]; ring
  · ring_nf

end X4PD

namespace X4PD

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

lemma law (X Y : Matrix (Fin n) (Fin n) ℝ) (V : Mq n) :
    noiseA (passiveMatrix X Y * V * (passiveMatrix X Y).transpose) =
        unitaryParameter X Y * noiseA V * (unitaryParameter X Y).conjTranspose ∧
    noiseB (passiveMatrix X Y * V * (passiveMatrix X Y).transpose) =
        unitaryParameter X Y * noiseB V * (unitaryParameter X Y).transpose := by
  have hc : complexForm (passiveMatrix X Y * V * (passiveMatrix X Y).transpose) =
      complexForm (passiveMatrix X Y) * complexForm V * (complexForm (passiveMatrix X Y))ᴴ := by
    rw [cf_mul, cf_mul, cfH']
  rw [X4PM.part2] at hc
  unfold noiseA noiseB
  rw [hc]
  constructor <;> ext i j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks]

lemma diag_mul_symm {M N : Matrix (Fin n) (Fin n) ℂ} (hM : IsDiagonal M) (hN : IsDiagonal N) :
    (M * N).IsSymm := by
  have key : ∀ i j, i ≠ j → (M * N) i j = 0 := by
    intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : i = k
    · subst hk; rw [hN i j hij, mul_zero]
    · rw [hM i k hk, zero_mul]
  apply Matrix.IsSymm.ext
  intro i j
  by_cases h : i = j
  · subst h; rfl
  · rw [key i j h, key j i (Ne.symm h)]

lemma symm_tr (V : Mq n) (hV : V.PosDef) : Vᵀ = V := by
  have := hV.isHermitian
  unfold Matrix.IsHermitian at this
  rwa [conjTranspose_eq_transpose_of_trivial] at this

end X4PD


-- ===== PDMain

open scoped InnerProductSpace RealInnerProductSpace
open Module
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4PD

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

lemma inner_eq (x y : EuclideanSpace ℝ (Phase n)) :
    ⟪x, y⟫ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma sT_sT : (sigma n)ᵀ * (sigma n)ᵀ = -1 := by
  rw [X4SF.sigma_transpose, neg_mul_neg, X4SF.sigma_mul_sigma]

lemma exists_diag (V : Mq n) (hV : Vᵀ = V)
    (hc : V * (sigma n * V * sigma n) = (sigma n * V * sigma n) * V) :
    ∃ K : Mq n, IsPassive K ∧ IsDiagonal (K * V * K.transpose) := by
  let T : (EuclideanSpace ℝ (Phase n)) →ₗ[ℝ] (EuclideanSpace ℝ (Phase n)) := Matrix.toEuclideanLin V
  let J : (EuclideanSpace ℝ (Phase n)) →ₗ[ℝ] (EuclideanSpace ℝ (Phase n)) := Matrix.toEuclideanLin (sigma n)ᵀ
  have hTa : ∀ x : (EuclideanSpace ℝ (Phase n)), WithLp.ofLp (T x) = V *ᵥ WithLp.ofLp x := fun x => rfl
  have hJa : ∀ x : (EuclideanSpace ℝ (Phase n)), WithLp.ofLp (J x) = (sigma n)ᵀ *ᵥ WithLp.ofLp x := fun x => rfl
  have hT : T.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]; exact hV
  have hJ : ∀ x y : (EuclideanSpace ℝ (Phase n)), ⟪J x, J y⟫ = ⟪x, y⟫ := by
    intro x y
    rw [inner_eq, inner_eq, hJa, hJa, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec,
      X4SF.sigma_mul_sigmaT, one_mulVec]
  have hJJ : ∀ x : (EuclideanSpace ℝ (Phase n)), J (J x) = -x := by
    intro x
    apply (WithLp.linearEquiv 2 ℝ (Phase n → ℝ)).injective
    change WithLp.ofLp (J (J x)) = WithLp.ofLp (-x)
    rw [hJa, hJa, mulVec_mulVec, sT_sT, WithLp.ofLp_neg, neg_mulVec, one_mulVec]
  have hcm : V * (sigma n)ᵀ * V * (sigma n)ᵀ = (sigma n)ᵀ * V * (sigma n)ᵀ * V := by
    rw [X4SF.sigma_transpose]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simpa only [Matrix.mul_assoc] using hc
  have hcx : ∀ x : (EuclideanSpace ℝ (Phase n)), T (J (T (J x))) = J (T (J (T x))) := by
    intro x
    apply (WithLp.linearEquiv 2 ℝ (Phase n → ℝ)).injective
    change WithLp.ofLp (T (J (T (J x)))) = WithLp.ofLp (J (T (J (T x))))
    rw [hTa, hJa, hTa, hJa, hJa, hTa, hJa, hTa]
    simp only [mulVec_mulVec]
    congr 1
    simp only [← Matrix.mul_assoc]
    exact hcm
  have hE : finrank ℝ (EuclideanSpace ℝ (Phase n)) = 2 * n := by
    rw [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin]; ring
  obtain ⟨f, hfo, hfe⟩ := build hT hJ hJJ hcx n hE n le_rfl
  set g := fam J f with hg
  let K : Mq n := Matrix.of fun a c => WithLp.ofLp (g a) c
  have hrow : ∀ a, (fun c => K a c) = WithLp.ofLp (g a) := fun a => rfl
  have hKK : K * K.transpose = 1 := by
    ext a b
    have := (orthonormal_iff_ite.mp hfo) b a
    rw [inner_eq] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    change WithLp.ofLp (g a) ⬝ᵥ WithLp.ofLp (g b) = _
    rw [dotProduct_comm]
    rw [show (g = fam J f) from rfl] at *
    rw [this]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hKK' : K.transpose * K = 1 := mul_eq_one_comm.mp hKK
  have hKpm : K = passiveMatrix (Matrix.of fun i j => K (Sum.inl i) (Sum.inl j))
      (Matrix.of fun i j => K (Sum.inl i) (Sum.inr j)) := by
    ext a c
    rcases a with i | i
    · rcases c with j | j <;> rfl
    · have h1 : WithLp.ofLp (g (Sum.inr i)) = (sigma n)ᵀ *ᵥ WithLp.ofLp (g (Sum.inl i)) := hJa _
      have h2 : K (Sum.inr i) = (sigma n)ᵀ *ᵥ (fun c => K (Sum.inl i) c) := h1
      rcases c with j | j
      · change K (Sum.inr i) (Sum.inl j) = -K (Sum.inl i) (Sum.inr j)
        rw [h2]
        simp [mulVec, dotProduct, Fintype.sum_sum_type, X4PM.sig_eq,
          Matrix.one_apply, Matrix.fromBlocks]
      · change K (Sum.inr i) (Sum.inr j) = K (Sum.inl i) (Sum.inl j)
        rw [h2]
        simp [mulVec, dotProduct, Fintype.sum_sum_type, X4PM.sig_eq,
          Matrix.one_apply, Matrix.fromBlocks]
  have hpass : IsPassive K :=
    X4PM.passive_of_comm hKK' ((X4PM.comm_iff K).mpr ⟨_, _, hKpm⟩)
  refine ⟨K, hpass, ?_⟩
  intro a b hab
  obtain ⟨μ, hμ⟩ := hfe b
  have hev : V *ᵥ WithLp.ofLp (g b) = μ • WithLp.ofLp (g b) := by
    rw [← hTa, show T (g b) = μ • g b from hμ, WithLp.ofLp_smul]
  have hentry : (K * V * K.transpose) a b = WithLp.ofLp (g a) ⬝ᵥ (V *ᵥ WithLp.ofLp (g b)) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mulVec, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [K, Matrix.of_apply]; ring
  rw [hentry, hev, dotProduct_smul]
  have := (orthonormal_iff_ite.mp hfo) a b
  rw [inner_eq, if_neg hab] at this
  rw [this, smul_zero]

end X4PD


-- ===== PDWill

open scoped InnerProductSpace RealInnerProductSpace MatrixOrder
open Module
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4W

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix X4PD

variable {n : ℕ}

lemma good_perm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T J : E →ₗ[ℝ] E} {f : Fin n → E} (hf : Good T J f) (π : Equiv.Perm (Fin n)) :
    Good T J (f ∘ π) := by
  have h : fam J (f ∘ π) = fam J f ∘ Sum.map π π := by
    funext x; rcases x with x | x <;> rfl
  refine ⟨?_, fun x => ?_⟩
  · rw [h]; exact hf.1.comp _ (Sum.map_injective.mpr ⟨π.injective, π.injective⟩)
  · rw [h]; exact hf.2 _

lemma tr_of_psd {M : Mq n} (h : M.PosSemidef) : Mᵀ = M := by
  have := h.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma inner_eq' (x y : EuclideanSpace ℝ (Phase n)) :
    ⟪x, y⟫ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- Normal form of an invertible real skew matrix. -/
lemma skew_normal (M : Mq n) (hM : Mᵀ = -M) (hMu : IsUnit M.det) :
    ∃ O : Mq n, ∃ d : Fin n → ℝ, O * Oᵀ = 1 ∧ (∀ i, 0 < d i) ∧ Monotone (fun i => (d i)⁻¹) ∧
      O * M * Oᵀ = thermalCovariance d * sigma n := by
  set P := Mᵀ * M with hPdef
  have hPsd : P.PosSemidef := by
    have := posSemidef_conjTranspose_mul_self M
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hPu : IsUnit P.det := by
    rw [hPdef, det_mul, det_transpose]; exact hMu.mul hMu
  set Q := CFC.sqrt P with hQdef
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self P hPsd.nonneg
  have hQsd : Q.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hQu : IsUnit Q.det := by
    have := hPu; rw [← hQQ, det_mul] at this; exact isUnit_of_mul_isUnit_left this
  have hQpd : Q.PosDef := hQsd.posDef_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hQu)
  have hQt : Qᵀ = Q := tr_of_psd hQsd
  have hMM : M * M = -P := by rw [hPdef, hM, Matrix.neg_mul, neg_neg]
  have hPM : Commute P M := by
    show P * M = M * P
    rw [hPdef, hM]; simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hQM : Q * M = M * Q := by
    have := hPM.cfc_nnreal NNReal.sqrt
    rw [← CFC.sqrt_eq_cfc] at this
    exact this
  set Qi := Q⁻¹ with hQidef
  have hQiQ : Qi * Q = 1 := nonsing_inv_mul Q hQu
  have hQQi : Q * Qi = 1 := mul_nonsing_inv Q hQu
  have hQit : Qiᵀ = Qi := by rw [hQidef, transpose_nonsing_inv, hQt]
  have hQiM : Qi * M = M * Qi := by
    calc Qi * M = Qi * M * (Q * Qi) := by rw [hQQi, Matrix.mul_one]
      _ = Qi * (Q * M) * Qi := by rw [hQM]; simp only [Matrix.mul_assoc]
      _ = M * Qi := by rw [← Matrix.mul_assoc, hQiQ, Matrix.one_mul]
  set Jm := -(M * Qi) with hJmdef
  have hJJ : Jm * Jm = -1 := by
    rw [hJmdef, neg_mul_neg]
    calc M * Qi * (M * Qi) = M * M * (Qi * Qi) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qi M Qi, hQiM]; simp only [Matrix.mul_assoc]
      _ = -1 := by
          rw [hMM, ← hQQ, Matrix.neg_mul]
          congr 1
          calc Q * Q * (Qi * Qi) = Q * (Q * Qi) * Qi := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hQQi, Matrix.mul_one, hQQi]
  have hJtJ : Jmᵀ * Jm = 1 := by
    rw [hJmdef, transpose_neg, neg_mul_neg, transpose_mul, hQit, hM]
    calc Qi * -M * (M * Qi) = Qi * (-M * M) * Qi := by simp only [Matrix.mul_assoc]
      _ = Qi * (Q * Q) * Qi := by rw [Matrix.neg_mul, hMM, neg_neg, hQQ]
      _ = 1 := by
          calc Qi * (Q * Q) * Qi = (Qi * Q) * (Q * Qi) := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hQiQ, hQQi, Matrix.one_mul]
  have hQJ : Q * Jm = Jm * Q := by
    rw [hJmdef, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, hQM, Matrix.mul_assoc,
      hQQi, Matrix.mul_assoc, hQiQ]
  have hMJ : M = -(Jm * Q) := by
    rw [hJmdef, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hQiQ, Matrix.mul_one]
  -- operators
  let T : (EuclideanSpace ℝ (Phase n)) →ₗ[ℝ] (EuclideanSpace ℝ (Phase n)) := Matrix.toEuclideanLin Q
  let J : (EuclideanSpace ℝ (Phase n)) →ₗ[ℝ] (EuclideanSpace ℝ (Phase n)) := Matrix.toEuclideanLin Jm
  have hTa : ∀ x : (EuclideanSpace ℝ (Phase n)), WithLp.ofLp (T x) = Q *ᵥ WithLp.ofLp x := fun x => rfl
  have hJa : ∀ x : (EuclideanSpace ℝ (Phase n)), WithLp.ofLp (J x) = Jm *ᵥ WithLp.ofLp x := fun x => rfl
  have hT : T.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    exact hQsd.isHermitian
  have hJ : ∀ x y : (EuclideanSpace ℝ (Phase n)), ⟪J x, J y⟫ = ⟪x, y⟫ := by
    intro x y
    rw [inner_eq', inner_eq', hJa, hJa, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
      hJtJ, one_mulVec]
  have hJJx : ∀ x : (EuclideanSpace ℝ (Phase n)), J (J x) = -x := by
    intro x
    apply (WithLp.linearEquiv 2 ℝ (Phase n → ℝ)).injective
    change WithLp.ofLp (J (J x)) = WithLp.ofLp (-x)
    rw [hJa, hJa, mulVec_mulVec, hJJ, WithLp.ofLp_neg, neg_mulVec, one_mulVec]
  have key : Q * (Jm * (Q * Jm)) = Jm * (Q * (Jm * Q)) := by
    calc Q * (Jm * (Q * Jm)) = Q * Jm * Q * Jm := by simp only [Matrix.mul_assoc]
      _ = Jm * Q * Q * Jm := by rw [hQJ]
      _ = Jm * Q * (Q * Jm) := by simp only [Matrix.mul_assoc]
      _ = Jm * Q * (Jm * Q) := by rw [hQJ]
      _ = Jm * (Q * (Jm * Q)) := by simp only [Matrix.mul_assoc]
  have hcx : ∀ x : (EuclideanSpace ℝ (Phase n)), T (J (T (J x))) = J (T (J (T x))) := by
    intro x
    apply (WithLp.linearEquiv 2 ℝ (Phase n → ℝ)).injective
    change WithLp.ofLp (T (J (T (J x)))) = WithLp.ofLp (J (T (J (T x))))
    rw [hTa, hJa, hTa, hJa, hJa, hTa, hJa, hTa]
    simp only [mulVec_mulVec]
    congr 1
  have hE : finrank ℝ (EuclideanSpace ℝ (Phase n)) = 2 * n := by
    rw [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin]; ring
  obtain ⟨f0, hf0⟩ := build hT hJ hJJx hcx n hE n le_rfl
  -- eigenvalues
  let d0 : Fin n → ℝ := fun i => ⟪f0 i, T (f0 i)⟫
  have hev0 : ∀ i, T (f0 i) = d0 i • f0 i := by
    intro i
    obtain ⟨μ, hμ⟩ := hf0.2 (Sum.inl i)
    change T (f0 i) = μ • f0 i at hμ
    have h1 : ⟪f0 i, f0 i⟫ = 1 := by
      have := (orthonormal_iff_ite.mp hf0.1) (Sum.inl i) (Sum.inl i)
      simpa [fam] using this
    have : d0 i = μ := by
      show ⟪f0 i, T (f0 i)⟫ = μ
      rw [hμ, real_inner_smul_right, h1, mul_one]
    rw [this, hμ]
  let π := Tuple.sort (fun i => (d0 i)⁻¹)
  set f := f0 ∘ π with hfdef
  have hf : Good T J f := good_perm hf0 π
  set d := d0 ∘ π with hddef
  have hev : ∀ i, T (f i) = d i • f i := fun i => hev0 (π i)
  have hevJ : ∀ i, T (J (f i)) = d i • J (f i) := by
    intro i
    apply (WithLp.linearEquiv 2 ℝ (Phase n → ℝ)).injective
    change WithLp.ofLp (T (J (f i))) = WithLp.ofLp (d i • J (f i))
    rw [hTa, hJa, WithLp.ofLp_smul, hJa, mulVec_mulVec, hQJ, ← mulVec_mulVec, ← hTa, hev,
      WithLp.ofLp_smul, mulVec_smul]
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have h1 : ⟪f i, f i⟫ = 1 := by
      have := (orthonormal_iff_ite.mp hf.1) (Sum.inl i) (Sum.inl i)
      simpa [fam] using this
    have hne : WithLp.ofLp (f i) ≠ 0 := by
      intro h0
      rw [inner_eq', h0, zero_dotProduct] at h1
      exact zero_ne_one h1
    have := hQpd.dotProduct_mulVec_pos hne
    have e : star (WithLp.ofLp (f i)) ⬝ᵥ (Q *ᵥ WithLp.ofLp (f i)) = d i := by
      rw [star_trivial, ← hTa, hev, WithLp.ofLp_smul, dotProduct_smul, ← inner_eq', h1]
      simp
    rw [e] at this
    exact this
  -- the orthogonal matrix
  set g := fam J f with hg
  let O : Mq n := Matrix.of fun a c => WithLp.ofLp (g a) c
  have hOO : O * Oᵀ = 1 := by
    ext a b
    have := (orthonormal_iff_ite.mp hf.1) b a
    rw [inner_eq'] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    change WithLp.ofLp (g a) ⬝ᵥ WithLp.ofLp (g b) = _
    rw [dotProduct_comm]
    rw [show (g = fam J f) from rfl] at *
    rw [this]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hmono : Monotone (fun i => (d i)⁻¹) := Tuple.monotone_sort (fun i => (d0 i)⁻¹)
  refine ⟨O, d, hOO, hdpos, hmono, ?_⟩
  -- action of M on the rows
  have hMg : ∀ b : Phase n, M *ᵥ WithLp.ofLp (g b) = Sum.elim (fun j => -(d j) • WithLp.ofLp (g (Sum.inr j)))
      (fun j => d j • WithLp.ofLp (g (Sum.inl j))) b := by
    rintro (j | j)
    · simp only [Sum.elim_inl]
      change M *ᵥ WithLp.ofLp (f j) = -(d j) • WithLp.ofLp (J (f j))
      rw [hMJ, neg_mulVec, ← mulVec_mulVec, ← hTa, hev, WithLp.ofLp_smul, mulVec_smul, ← hJa,
        neg_smul]
    · simp only [Sum.elim_inr]
      change M *ᵥ WithLp.ofLp (J (f j)) = d j • WithLp.ofLp (f j)
      rw [hMJ, neg_mulVec, ← mulVec_mulVec, ← hTa, hevJ, WithLp.ofLp_smul, mulVec_smul, hJa,
        mulVec_mulVec, hJJ, neg_mulVec, one_mulVec, smul_neg, neg_neg]
  have hentry : ∀ a b, (O * M * Oᵀ) a b = WithLp.ofLp (g a) ⬝ᵥ (M *ᵥ WithLp.ofLp (g b)) := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mulVec, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [O, Matrix.of_apply]; ring
  have hdot : ∀ a b, WithLp.ofLp (g a) ⬝ᵥ WithLp.ofLp (g b) = if a = b then 1 else 0 := by
    intro a b
    rw [← inner_eq']; exact (orthonormal_iff_ite.mp hf.1) a b
  ext a b
  rw [hentry, hMg]
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Sum.elim_inl, Sum.elim_inr, dotProduct_smul, hdot, thermalCovariance, X4PM.sig_eq,
      fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg,
      add_zero, zero_add, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, reduceCtorEq, if_false, smul_zero,
      Sum.inl.injEq, Sum.inr.injEq, Matrix.zero_apply, Matrix.neg_apply, diagonal_apply, smul_eq_mul]
  all_goals (by_cases h : i = j <;> [(subst h; simp); simp [h, Ne.symm h]])

end X4W


-- ===== PDWillLib

open scoped InnerProductSpace RealInnerProductSpace MatrixOrder
open Module
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4W

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix X4PD

variable {n : ℕ}

lemma th_mul (a b : Fin n → ℝ) : thermalCovariance a * thermalCovariance b = thermalCovariance (a * b) := by
  simp [thermalCovariance, fromBlocks_multiply, diagonal_mul_diagonal]

lemma th_one : thermalCovariance (fun _ : Fin n => (1 : ℝ)) = 1 := by
  simp [thermalCovariance, ← fromBlocks_one]

lemma th_tr (a : Fin n → ℝ) : (thermalCovariance a)ᵀ = thermalCovariance a := by
  simp [thermalCovariance, fromBlocks_transpose]

lemma th_sigma (a : Fin n → ℝ) : thermalCovariance a * sigma n = sigma n * thermalCovariance a := by
  rw [thermalCovariance, X4PM.sig_eq, fromBlocks_multiply, fromBlocks_multiply]; simp

lemma williamson (V : Mq n) (hV : V.PosDef) :
    ∃ kappa : Fin n → ℝ, ∃ S : Mq n,
      (∀ i, 0 < kappa i) ∧ Monotone kappa ∧ PreservesCanonicalForm S ∧
      S * V * S.transpose = thermalCovariance kappa ∧
      S * (-V) * S.transpose = -thermalCovariance kappa := by
  set R := CFC.sqrt V with hRdef
  have hRR : R * R = V := CFC.sqrt_mul_sqrt_self V hV.posSemidef.nonneg
  have hRsd : R.PosSemidef := (CFC.sqrt_nonneg V).posSemidef
  have hRt : Rᵀ = R := tr_of_psd hRsd
  have hVu : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit
  have hRu : IsUnit R.det := by
    have := hVu; rw [← hRR, det_mul] at this; exact isUnit_of_mul_isUnit_left this
  set Ri := R⁻¹ with hRidef
  have hRit : Riᵀ = Ri := by rw [hRidef, transpose_nonsing_inv, hRt]
  have hRiu : IsUnit Ri.det := by rw [hRidef]; exact (Matrix.isUnit_nonsing_inv_det_iff).mpr hRu
  have hRiVRi : Ri * V * Ri = 1 := by
    rw [← hRR]
    calc Ri * (R * R) * Ri = (Ri * R) * (R * Ri) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul R hRu, mul_nonsing_inv R hRu, Matrix.one_mul]
  set M := Ri * sigma n * Ri with hMdef
  have hMt : Mᵀ = -M := by
    rw [hMdef, transpose_mul, transpose_mul, hRit, X4SF.sigma_transpose]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hsu : IsUnit (sigma n).det := by
    have h := congrArg Matrix.det (X4SF.sigma_mul_sigmaT (n := n))
    rw [det_mul, det_one] at h
    exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  have hMu : IsUnit M.det := by
    rw [hMdef, det_mul, det_mul]; exact (hRiu.mul hsu).mul hRiu
  obtain ⟨O, d, hOO, hdpos, hmono, hOM⟩ := skew_normal M hMt hMu
  set lam : Fin n → ℝ := fun i => (Real.sqrt (d i))⁻¹ with hlam
  set L := thermalCovariance lam with hL
  have hlam2 : lam * lam = fun i => (d i)⁻¹ := by
    funext i
    simp only [Pi.mul_apply, hlam]
    rw [← mul_inv, Real.mul_self_sqrt (hdpos i).le]
  have hlamd : lam * d * lam = fun _ => 1 := by
    funext i
    simp only [Pi.mul_apply, hlam]
    have := Real.mul_self_sqrt (hdpos i).le
    have hs : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr (hdpos i)
    field_simp
    linarith
  refine ⟨fun i => (d i)⁻¹, L * O * Ri, fun i => inv_pos.mpr (hdpos i), hmono, ?_, ?_, ?_⟩
  · unfold PreservesCanonicalForm
    rw [transpose_mul, transpose_mul, hRit, th_tr]
    calc L * O * Ri * sigma n * (Ri * (Oᵀ * L)) = L * (O * M * Oᵀ) * L := by
          simp only [hMdef, Matrix.mul_assoc]
      _ = thermalCovariance lam * thermalCovariance d * (sigma n * thermalCovariance lam) := by
          rw [hOM, hL]; simp only [Matrix.mul_assoc]
      _ = thermalCovariance lam * thermalCovariance d * thermalCovariance lam * sigma n := by
          rw [← th_sigma lam]; simp only [Matrix.mul_assoc]
      _ = sigma n := by rw [th_mul, th_mul, hlamd, th_one, Matrix.one_mul]
  · have : L * O * Ri * V * (L * O * Ri)ᵀ = thermalCovariance (lam * lam) := by
      rw [transpose_mul, transpose_mul, hRit, th_tr, ← th_mul]
      calc L * O * Ri * V * (Ri * (Oᵀ * L)) = L * O * (Ri * V * Ri) * Oᵀ * L := by
            simp only [Matrix.mul_assoc]
        _ = L * L := by rw [hRiVRi, Matrix.mul_one, Matrix.mul_assoc L O, hOO, Matrix.mul_one]
    rw [this, hlam2]
  · have : L * O * Ri * V * (L * O * Ri)ᵀ = thermalCovariance (lam * lam) := by
      rw [transpose_mul, transpose_mul, hRit, th_tr, ← th_mul]
      calc L * O * Ri * V * (Ri * (Oᵀ * L)) = L * O * (Ri * V * Ri) * Oᵀ * L := by
            simp only [Matrix.mul_assoc]
        _ = L * L := by rw [hRiVRi, Matrix.mul_one, Matrix.mul_assoc L O, hOO, Matrix.mul_one]
    rw [Matrix.mul_neg, Matrix.neg_mul, this, hlam2]

end X4W



-- ===== PDWillSol

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n)
    (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.PosDef) :
    ∃ kappa : Fin n → ℝ, ∃ S : Matrix (Phase n) (Phase n) ℝ,
      (∀ i, 0 < kappa i) ∧ Monotone kappa ∧ PreservesCanonicalForm S ∧
      S * V * S.transpose = thermalCovariance kappa ∧
      S * (-V) * S.transpose = -thermalCovariance kappa :=
  X4W.williamson V hV

