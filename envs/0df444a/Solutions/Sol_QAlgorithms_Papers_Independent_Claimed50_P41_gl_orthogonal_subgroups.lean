-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.gl_orthogonal_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:21.594807+00:00
-- url     : https://prove2.me/submissions/0123f2b9-2e56-4060-adce-d73ff1892c05

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

open MeasureTheory
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Claimed50.P41 X4GL in
theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det → PreservesCanonicalForm (glMatrix A)) ∧
    (∀ A B : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det → IsUnit B.det →
      glMatrix (A * B) = glMatrix A * glMatrix B) ∧
    Function.Injective (@glMatrix n) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det →
      (A⁻¹.transpose = A ↔ A.transpose * A = 1)) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A.transpose * A = 1 →
      IsPassive (Matrix.fromBlocks A 0 0 A)) ∧
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, IsUnit A.det ∧ S = glMatrix A} = (n ^ 2 : ℕ) ∧
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ S = glMatrix A} =
      (n * (n - 1) / 2 : ℕ) ∧
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ A.det = 1 ∧ S = glMatrix A} =
      (n * (n - 1) / 2 : ℕ) := ⟨part1, part2, part3, part4, part5, part6 hn, part7, part8⟩
