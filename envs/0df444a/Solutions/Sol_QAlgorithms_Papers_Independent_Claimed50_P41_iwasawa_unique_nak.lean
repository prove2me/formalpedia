-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.iwasawa_unique_nak
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:42:22.827138+00:00
-- url     : https://prove2.me/submissions/87accd61-ea01-4b74-903d-bdbf6d8dafe6

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


open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4PreIwasawa

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


abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

lemma complexify_mul (P Q : Sq n) : complexify (P * Q) = complexify P * complexify Q := by
  ext i j
  simp [complexify, Matrix.mul_apply]

lemma tr_of_psd {M : Sq n} (h : M.PosSemidef) : M.transpose = M := by
  have := h.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- Block relations of a symplectic matrix and of its transpose. -/
structure Rel (A B C D : Sq n) : Prop where
  s11 : A * B.transpose = B * A.transpose
  s12 : A * D.transpose = 1 + B * C.transpose
  t11 : A.transpose * C = C.transpose * A
  t12 : C.transpose * B = A.transpose * D - 1
  t21 : D.transpose * A = B.transpose * C + 1
  t22 : D.transpose * B = B.transpose * D

lemma rel_of {A B C D : Sq n} (hS : PreservesCanonicalForm (Matrix.fromBlocks A B C D)) :
    Rel A B C D := by
  have hT := symp_transpose hS
  unfold PreservesCanonicalForm sigma at hS hT
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hS
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_transpose, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hT
  obtain ⟨a1, a2, -, -⟩ := hS
  obtain ⟨b1, b2, b3, b4⟩ := hT
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
    Matrix.neg_mul] at a1 a2 b1 b2 b3 b4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((neg_add_eq_zero).mp a1).symm
  · rw [← a2]; abel
  · exact ((neg_add_eq_zero).mp b1).symm
  · rw [← b2]; abel
  · calc D.transpose * A = -(-(D.transpose * A) + B.transpose * C) + B.transpose * C := by abel
      _ = _ := by rw [b3]; abel
  · exact ((neg_add_eq_zero).mp b4)


lemma inv_tr {M : Sq n} (h : M.transpose = M) : (M⁻¹).transpose = M⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, h]

/-- Basic data: `G = AAᵀ + BBᵀ`, `H' = CAᵀ + DBᵀ`. -/
lemma G_facts {A B C D : Sq n} (hS : PreservesCanonicalForm (Matrix.fromBlocks A B C D)) :
    (A * A.transpose + B * B.transpose).PosDef ∧
    (A * A.transpose + B * B.transpose) * (C * A.transpose + D * B.transpose) =
      (A * C.transpose + B * D.transpose) * (A * A.transpose + B * B.transpose) := by
  have hSu := symp_isUnit hS
  set S := Matrix.fromBlocks A B C D with hSdef
  have hSS : (S * S.transpose).PosDef := by
    have := Matrix.PosDef.mul_conjTranspose_self S (fun x y hxy => by
      have := congrArg (fun z => z ᵥ* S⁻¹) hxy
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hSu] using this)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hblk : S * S.transpose = Matrix.fromBlocks (A * A.transpose + B * B.transpose)
      (A * C.transpose + B * D.transpose) (C * A.transpose + D * B.transpose)
      (C * C.transpose + D * D.transpose) := by
    rw [hSdef, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  have hSSs : PreservesCanonicalForm (S * S.transpose) := symp_mul hS (symp_transpose hS)
  rw [hblk] at hSS hSSs
  refine ⟨?_, ?_⟩
  · have := hSS.submatrix (e := Sum.inl) Sum.inl_injective
    exact this
  · have r := (rel_of hSSs).s11
    have hGt : (A * A.transpose + B * B.transpose).transpose = A * A.transpose + B * B.transpose := by
      simp [Matrix.transpose_add, Matrix.transpose_mul]
    rw [hGt] at r
    rw [← r]
    congr 1
    simp [Matrix.transpose_add, Matrix.transpose_mul]

lemma passive_of (X Y : Sq n) (hXX : X * X.transpose + Y * Y.transpose = 1)
    (hXY : X * Y.transpose = Y * X.transpose) : IsPassive (passiveMatrix X Y) := by
  have hKt : (passiveMatrix X Y).transpose =
      Matrix.fromBlocks X.transpose (-Y.transpose) Y.transpose X.transpose := by
    unfold passiveMatrix; rw [Matrix.fromBlocks_transpose, Matrix.transpose_neg]
  have hKKt : passiveMatrix X Y * (passiveMatrix X Y).transpose = 1 := by
    rw [hKt]; unfold passiveMatrix
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      (try simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]) <;>
      first
      | exact hXX
      | (rw [add_comm]; exact hXX)
      | (rw [hXY]; abel)
  refine ⟨?_, mul_eq_one_comm.mp hKKt⟩
  unfold PreservesCanonicalForm
  rw [hKt]; unfold passiveMatrix sigma
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
      Matrix.neg_mul, neg_neg] <;>
    first
    | exact hXX
    | (rw [add_comm]; exact hXX)
    | (rw [← neg_add, hXX])
    | (rw [← neg_add, add_comm, hXX])
    | (rw [hXY]; abel)

end X4PreIwasawa



open scoped Matrix.Norms.Frobenius
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4Iw

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def LT (A : Sq n) : Prop := ∀ i j, i < j → A i j = 0

def ULT (A : Sq n) : Prop := (∀ i, A i i = 1) ∧ LT A

lemma LT.lower {A : Sq n} (h : LT A) : A.IsLowerTriangular := fun i j hij => h i j hij

lemma lt_mul {A B : Sq n} (hA : LT A) (hB : LT B) : LT (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (lt_of_le_of_lt h hij), mul_zero]

lemma lt_mul_diag {A B : Sq n} (hA : LT A) (hB : LT B) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hB k i h, mul_zero]
    · rw [hA i k h, zero_mul]
  · simp

lemma ult_mul {A B : Sq n} (hA : ULT A) (hB : ULT B) : ULT (A * B) :=
  ⟨fun i => by rw [lt_mul_diag hA.2 hB.2, hA.1, hB.1, one_mul], lt_mul hA.2 hB.2⟩

lemma ult_det {A : Sq n} (hA : ULT A) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A hA.2.lower]; simp [hA.1]

lemma ult_unit {A : Sq n} (hA : ULT A) : IsUnit A.det := by rw [ult_det hA]; exact isUnit_one

lemma lt_inv {A : Sq n} (hA : LT A) (hu : IsUnit A.det) : LT A⁻¹ := by
  letI := A.invertibleOfIsUnitDet hu
  have := Matrix.blockTriangular_inv_of_blockTriangular hA.lower
  exact fun i j hij => this hij

lemma ult_inv {A : Sq n} (hA : ULT A) : ULT A⁻¹ := by
  have hl := lt_inv hA.2 (ult_unit hA)
  refine ⟨fun i => ?_, hl⟩
  have := lt_mul_diag hl hA.2 i
  rw [Matrix.nonsing_inv_mul _ (ult_unit hA), hA.1, mul_one] at this
  simpa using this.symm

lemma ldl_unique {A1 A2 : Sq n} (h1 : ULT A1) (h2 : ULT A2) {d1 d2 : Fin n → ℝ}
    (hd : ∀ i, d1 i ≠ 0)
    (h : A1 * diagonal d1 * A1ᵀ = A2 * diagonal d2 * A2ᵀ) : A1 = A2 ∧ d1 = d2 := by
  have u1 := ult_unit h1
  have u2 := ult_unit h2
  set P := A2⁻¹ * A1 with hP
  set Q := A1⁻¹ * A2 with hQ
  have hPu : ULT P := ult_mul (ult_inv h2) h1
  have hQu : ULT Q := ult_mul (ult_inv h1) h2
  have key : P * diagonal d1 = diagonal d2 * Qᵀ := by
    rw [hP, hQ, Matrix.transpose_mul]
    calc A2⁻¹ * A1 * diagonal d1 = A2⁻¹ * (A1 * diagonal d1 * A1ᵀ) * (A1⁻¹)ᵀ := by
          simp only [Matrix.mul_assoc]
          rw [show A1ᵀ * A1⁻¹ᵀ = 1 by
            rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ u1, Matrix.transpose_one], Matrix.mul_one]
      _ = A2⁻¹ * (A2 * diagonal d2 * A2ᵀ) * (A1⁻¹)ᵀ := by rw [h]
      _ = diagonal d2 * (A2ᵀ * A1⁻¹ᵀ) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc A2⁻¹ A2, Matrix.nonsing_inv_mul _ u2, Matrix.one_mul]
  have hP1 : P = 1 := by
    ext i j
    have e := congrFun (congrFun key i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply] at e
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [hPu.2 i j hij, Matrix.one_apply_ne (ne_of_lt hij)]
    · rw [hPu.1, Matrix.one_apply_eq]
    · rw [hQu.2 j i hij, mul_zero] at e
      rw [Matrix.one_apply_ne (ne_of_gt hij)]
      exact (mul_eq_zero.mp e).resolve_right (hd j)
  have hA : A1 = A2 := by
    have : A2 * P = A1 := by
      rw [hP, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ u2, Matrix.one_mul]
    rw [← this, hP1, Matrix.mul_one]
  refine ⟨hA, funext fun i => ?_⟩
  have e := congrFun (congrFun key i) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, hPu.1, hQu.1] at e
  linarith

abbrev Mt (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

lemma nd_eq (A C E : Sq n) (κ : Fin n → ℝ) : fromBlocks A 0 C E * squeezeMatrix κ =
    fromBlocks (A * diagonal κ) 0 (C * diagonal κ) (E * diagonal (fun i => (κ i)⁻¹)) := by
  unfold squeezeMatrix
  rw [fromBlocks_multiply]; simp

lemma sst_blocks (A C E : Sq n) (κ : Fin n → ℝ) :
    ((fromBlocks A 0 C E * squeezeMatrix κ) * (fromBlocks A 0 C E * squeezeMatrix κ)ᵀ).toBlocks₁₁ =
      A * diagonal (fun i => κ i * κ i) * Aᵀ ∧
    ((fromBlocks A 0 C E * squeezeMatrix κ) * (fromBlocks A 0 C E * squeezeMatrix κ)ᵀ).toBlocks₁₂ =
      A * diagonal (fun i => κ i * κ i) * Cᵀ := by
  rw [nd_eq, fromBlocks_transpose, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.transpose_mul, diagonal_transpose,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  constructor <;> rw [Matrix.mul_assoc A, ← Matrix.mul_assoc (diagonal κ), diagonal_mul_diagonal,
    ← Matrix.mul_assoc]

lemma unit_N {A C : Sq n} (hA : ULT A) : IsUnit (fromBlocks A 0 C A⁻¹ᵀ).det := by
  rw [det_fromBlocks_zero₁₂, det_transpose, det_nonsing_inv, ult_det hA]; simp

lemma unit_D {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) : IsUnit (squeezeMatrix κ).det := by
  unfold squeezeMatrix
  rw [det_fromBlocks_zero₁₂, det_diagonal, det_diagonal]
  refine (IsUnit.mul ?_ ?_) <;> refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
  · exact (hκ i).ne'
  · exact inv_ne_zero (hκ i).ne'

lemma iw_unique {S : Mt n} (f g : Mt n × (Fin n → ℝ) × Mt n)
    (hf : IsNilpotentFactor f.1 ∧ (∀ i, 0 < f.2.1 i) ∧ IsPassive f.2.2 ∧
      S = f.1 * squeezeMatrix f.2.1 * f.2.2)
    (hg : IsNilpotentFactor g.1 ∧ (∀ i, 0 < g.2.1 i) ∧ IsPassive g.2.2 ∧
      S = g.1 * squeezeMatrix g.2.1 * g.2.2) : f = g := by
  obtain ⟨N1, κ1, K1⟩ := f
  obtain ⟨N2, κ2, K2⟩ := g
  obtain ⟨⟨A1, C1, hA1d, hA1l, -, rfl⟩, hk1, hK1, hS1⟩ := hf
  obtain ⟨⟨A2, C2, hA2d, hA2l, -, rfl⟩, hk2, hK2, hS2⟩ := hg
  simp only at hk1 hK1 hS1 hk2 hK2 hS2 ⊢
  have u1 : ULT A1 := ⟨hA1d, hA1l⟩
  have u2 : ULT A2 := ⟨hA2d, hA2l⟩
  have hSS : ∀ (A C : Sq n) κ (K : Mt n), IsPassive K → S = fromBlocks A 0 C A⁻¹ᵀ * squeezeMatrix κ * K →
      S * Sᵀ = (fromBlocks A 0 C A⁻¹ᵀ * squeezeMatrix κ) * (fromBlocks A 0 C A⁻¹ᵀ * squeezeMatrix κ)ᵀ := by
    intro A C κ K hK hS
    have hKK : K * Kᵀ = 1 := mul_eq_one_comm.mp hK.2
    rw [hS, Matrix.transpose_mul (_ * _) K, Matrix.mul_assoc, ← Matrix.mul_assoc K, hKK, Matrix.one_mul]
  have e1 := sst_blocks A1 C1 A1⁻¹ᵀ κ1
  have e2 := sst_blocks A2 C2 A2⁻¹ᵀ κ2
  rw [← hSS _ _ _ _ hK1 hS1] at e1
  rw [← hSS _ _ _ _ hK2 hS2] at e2
  obtain ⟨hA, hd⟩ := ldl_unique u1 u2 (fun i => (mul_pos (hk1 i) (hk1 i)).ne') (e1.1.symm.trans e2.1)
  subst hA
  have hκ : κ1 = κ2 := funext fun i => by
    have := congrFun hd i
    nlinarith [hk1 i, hk2 i]
  subst hκ
  have hC : C1 = C2 := by
    have h12 := e1.2.symm.trans e2.2
    have hu : IsUnit (A1 * diagonal (fun i => κ1 i * κ1 i)) := by
      rw [Matrix.isUnit_iff_isUnit_det, det_mul, det_diagonal]
      refine (ult_unit u1).mul (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_))
      exact (mul_pos (hk1 i) (hk1 i)).ne'
    have := hu.mul_left_cancel h12
    simpa using congrArg Matrix.transpose this
  subst hC
  have hK : K1 = K2 := by
    have hu : IsUnit (fromBlocks A1 0 C1 A1⁻¹ᵀ * squeezeMatrix κ1) := by
      rw [Matrix.isUnit_iff_isUnit_det, det_mul]; exact (unit_N u1).mul (unit_D hk1)
    exact hu.mul_left_cancel (hS1.symm.trans hS2)
  rw [hK]

lemma ldl_exists {G : Sq n} (hG : G.PosDef) :
    ∃ L : Sq n, ULT L ∧ ∃ e : Fin n → ℝ, (∀ i, 0 < e i) ∧ G = L * diagonal e * Lᵀ := by
  have hT := LDL.lower_conj_diag hG
  set T := LDL.lower hG with hTdef
  rw [conjTranspose_eq_transpose_of_trivial] at hT
  have hTl : LT T := by
    have hu : IsUnit (LDL.lowerInv hG).det := isUnit_det_of_invertible _
    exact lt_inv (fun i j hij => LDL.lowerInv_triangular hG hij) hu
  have hTu : IsUnit T.det := Matrix.isUnit_nonsing_inv_det _ (isUnit_det_of_invertible _)
  have ht : ∀ i, T i i ≠ 0 := by
    have := isUnit_iff_ne_zero.mp hTu
    rw [Matrix.det_of_isLowerTriangular T hTl.lower] at this
    exact fun i => Finset.prod_ne_zero_iff.mp this i (Finset.mem_univ _)
  set L := T * diagonal (fun i => (T i i)⁻¹) with hL
  have hLu : ULT L := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [hL, mul_diagonal, mul_inv_cancel₀ (ht i)]
    · rw [hL, mul_diagonal, hTl i j hij, zero_mul]
  have hTL : T = L * diagonal (fun i => T i i) := by
    ext i j; rw [hL, mul_diagonal, mul_diagonal, inv_mul_cancel_right₀ (ht j)]
  set e : Fin n → ℝ := fun i => T i i * LDL.diagEntries hG i * T i i with he
  have hGe : G = L * diagonal e * Lᵀ := by
    rw [← hT, hTL, LDL.diag, Matrix.transpose_mul, diagonal_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal (LDL.diagEntries hG)), ← Matrix.mul_assoc (diagonal fun i => T i i),
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 3; funext i; rw [he]; ring
  refine ⟨L, hLu, e, fun i => ?_, hGe⟩
  have hp : (L * diagonal e * star L).PosDef := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, ← hGe]; exact hG
  have hLU : IsUnit L := (Matrix.isUnit_iff_isUnit_det _).mpr (ult_unit hLu)
  have := ((Matrix.IsUnit.posDef_star_right_conjugate_iff hLU).mp hp).diag_pos (i := i)
  simpa using this

lemma sq_mul (κ μ : Fin n → ℝ) : squeezeMatrix κ * squeezeMatrix μ = squeezeMatrix (κ * μ) := by
  unfold squeezeMatrix
  rw [fromBlocks_multiply]; simp [diagonal_mul_diagonal]; intro b; ring

lemma sq_inv_mul {κ : Fin n → ℝ} (hκ : ∀ i, κ i ≠ 0) :
    squeezeMatrix (fun i => (κ i)⁻¹) * squeezeMatrix κ = 1 := by
  rw [sq_mul]
  have : ((fun i => (κ i)⁻¹) * κ) = fun _ => 1 := funext fun i => by simp [hκ i]
  rw [this]; unfold squeezeMatrix; simp [← fromBlocks_one]

lemma sq_symp {κ : Fin n → ℝ} (hκ : ∀ i, κ i ≠ 0) : PreservesCanonicalForm (squeezeMatrix κ) := by
  unfold PreservesCanonicalForm squeezeMatrix sigma
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [diagonal_transpose, Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, diagonal_mul_diagonal]
  have h1 : (fun i => κ i * (κ i)⁻¹) = fun _ => (1 : ℝ) := funext fun i => mul_inv_cancel₀ (hκ i)
  have h2 : (fun i => (κ i)⁻¹ * κ i) = fun _ => (1 : ℝ) := funext fun i => inv_mul_cancel₀ (hκ i)
  rw [h1, h2, diagonal_one, neg_zero]

open X4PreIwasawa in
lemma iw_exists {S : Mt n} (hS : PreservesCanonicalForm S) :
    ∃ f : Mt n × (Fin n → ℝ) × Mt n, IsNilpotentFactor f.1 ∧ (∀ i, 0 < f.2.1 i) ∧ IsPassive f.2.2 ∧
      S = f.1 * squeezeMatrix f.2.1 * f.2.2 := by
  set A := S.toBlocks₁₁
  set B := S.toBlocks₁₂
  set C := S.toBlocks₂₁
  set D := S.toBlocks₂₂
  have hSb : S = fromBlocks A B C D := (fromBlocks_toBlocks S).symm
  have hS' : PreservesCanonicalForm (fromBlocks A B C D) := hSb ▸ hS
  obtain ⟨hG, -⟩ := G_facts hS'
  have hr := rel_of hS'
  obtain ⟨L, hLu, e, he, hGe⟩ := ldl_exists hG
  set κ : Fin n → ℝ := fun i => Real.sqrt (e i) with hκdef
  have hκ : ∀ i, 0 < κ i := fun i => Real.sqrt_pos.mpr (he i)
  set M := L * diagonal κ with hM
  have hMu : IsUnit M.det := by
    rw [hM, det_mul, det_diagonal]
    exact (ult_unit hLu).mul (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (hκ i).ne'))
  have hGM : A * Aᵀ + B * Bᵀ = M * Mᵀ := by
    rw [hGe, hM, Matrix.transpose_mul, diagonal_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal κ) (diagonal κ), diagonal_mul_diagonal]
    congr 2; congr 1; funext i; exact (Real.mul_self_sqrt (he i).le).symm
  set X' := M⁻¹ * A
  set Y' := M⁻¹ * B
  have hXX : X' * X'ᵀ + Y' * Y'ᵀ = 1 := by
    have : X' * X'ᵀ + Y' * Y'ᵀ = M⁻¹ * (A * Aᵀ + B * Bᵀ) * M⁻¹ᵀ := by
      simp only [X', Y', Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    rw [this, hGM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu, Matrix.one_mul,
      ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hMu, Matrix.transpose_one]
  have hXY : X' * Y'ᵀ = Y' * X'ᵀ := by
    simp only [X', Y', Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B, hr.s11]
  have hK0 := passive_of X' Y' hXX hXY
  set K0 := passiveMatrix X' Y'
  set N0 := S * K0ᵀ * squeezeMatrix (fun i => (κ i)⁻¹) with hN0
  have hdec : S = N0 * squeezeMatrix κ * K0 := by
    rw [hN0]; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (squeezeMatrix κ), sq_inv_mul (fun i => (hκ i).ne'), Matrix.one_mul, hK0.2,
      Matrix.mul_one]
  have hN0s : PreservesCanonicalForm N0 :=
    symp_mul (symp_mul hS (symp_transpose hK0.1)) (sq_symp fun i => (inv_pos.mpr (hκ i)).ne')
  have h11 : A * X'ᵀ + B * Y'ᵀ = M := by
    simp only [X', Y', Matrix.transpose_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hGM, Matrix.mul_assoc,
      ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hMu, Matrix.transpose_one, Matrix.mul_one]
  have h12 : -(A * Y'ᵀ) + B * X'ᵀ = 0 := by
    simp only [X', Y', Matrix.transpose_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hr.s11]; abel
  have hblk : N0 = fromBlocks L 0 N0.toBlocks₂₁ N0.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks N0]
    congr 1
    · rw [hN0, hSb]; unfold K0 passiveMatrix squeezeMatrix
      rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
      simp only [toBlocks_fromBlocks₁₁, Matrix.transpose_neg, Matrix.mul_zero, add_zero]
      rw [h11, hM, Matrix.mul_assoc, diagonal_mul_diagonal]
      convert Matrix.mul_one L
      rw [← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hκ i).ne'
    · rw [hN0, hSb]; unfold K0 passiveMatrix squeezeMatrix
      rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
      simp only [toBlocks_fromBlocks₁₂, Matrix.transpose_neg, Matrix.mul_zero, zero_add, Matrix.mul_neg]
      rw [h12, Matrix.zero_mul]
  refine ⟨(N0, κ, K0), ⟨L, N0.toBlocks₂₁, hLu.1, hLu.2, ?_, ?_⟩, hκ, hK0, hdec⟩
  · have r := rel_of (hblk ▸ hN0s)
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]; exact r.t11.symm
  · have r := rel_of (hblk ▸ hN0s)
    have h := r.s12
    rw [Matrix.zero_mul, add_zero] at h
    have hinv : L⁻¹ = N0.toBlocks₂₂ᵀ := Matrix.inv_eq_right_inv h
    conv_lhs => rw [hblk]
    rw [hinv, Matrix.transpose_transpose]

end X4Iw


open scoped Matrix.Norms.Frobenius
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4IwOne

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

lemma one_mode (S : Matrix (Phase 1) (Phase 1) ℝ) (hS : PreservesCanonicalForm S) :
      let a := S (Sum.inl 0) (Sum.inl 0)
      let b := S (Sum.inl 0) (Sum.inr 0)
      let c := S (Sum.inr 0) (Sum.inl 0)
      let d := S (Sum.inr 0) (Sum.inr 0)
      let xi := (a * c + b * d) / (a ^ 2 + b ^ 2)
      let eta := Real.log (a ^ 2 + b ^ 2)
      let phi := 2 * Complex.arg ((a : ℂ) - Complex.I * (b : ℂ))
      0 < a ^ 2 + b ^ 2 ∧ -2 * Real.pi < phi ∧ phi ≤ 2 * Real.pi ∧
      S = lensMatrix (fun _ _ => xi) * squeezeMatrix (fun _ => Real.exp (eta / 2)) *
        passiveMatrix (fun _ _ => Real.cos (phi / 2)) (fun _ _ => -Real.sin (phi / 2)) := by
  intro a b c d xi eta phi
  have hdet : a * d - b * c = 1 := by
    have := congrFun (congrFun hS (Sum.inl 0)) (Sum.inr 0)
    simp [sigma, Matrix.mul_apply, Fintype.sum_sum_type] at this
    simp only [a, b, c, d]; linarith
  have hs : 0 < a ^ 2 + b ^ 2 := by
    by_contra h
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    rw [ha, hb] at hdet; simp at hdet
  set z : ℂ := (a : ℂ) - Complex.I * (b : ℂ) with hz
  set k := Real.sqrt (a ^ 2 + b ^ 2) with hk
  have hkpos : 0 < k := Real.sqrt_pos.mpr hs
  have hk2 : k ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hs.le
  have hnz : ‖z‖ = k := by
    rw [hk, Complex.norm_def, Complex.normSq_apply]; congr 1; simp [hz]; ring
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hnz; linarith
  have hphi : phi / 2 = Complex.arg z := by simp only [phi]; ring
  have hcos : Real.cos (phi / 2) = a / k := by
    rw [hphi, Complex.cos_arg hz0, hnz]; simp [hz]
  have hsin : Real.sin (phi / 2) = -b / k := by
    rw [hphi, Complex.sin_arg, hnz]; simp [hz]
  have hexp : Real.exp (eta / 2) = k := by
    have h : Real.exp (eta / 2) * Real.exp (eta / 2) = a ^ 2 + b ^ 2 := by
      rw [← Real.exp_add, add_halves, Real.exp_log hs]
    rw [hk]; symm
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)]; exact h
  refine ⟨hs, ?_, ?_, ?_⟩
  · have := Complex.neg_pi_lt_arg z; simp only [phi]; linarith
  · have := Complex.arg_le_pi z; simp only [phi]; linarith
  rw [hcos, hsin, hexp]
  rw [show lensMatrix (n := 1) (fun _ _ => xi) = fromBlocks 1 0 (Matrix.of fun _ _ => xi) 1 from rfl,
    show passiveMatrix (n := 1) (fun _ _ => a / k) (fun _ _ => -(-b / k)) =
      fromBlocks (Matrix.of fun _ _ => a / k) (Matrix.of fun _ _ => -(-b / k))
        (-(Matrix.of fun _ _ => -(-b / k))) (Matrix.of fun _ _ => a / k) from rfl]
  unfold squeezeMatrix
  rw [fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_toBlocks S, fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]
  all_goals field_simp
  · rfl
  · rfl
  all_goals have hx : xi * (a ^ 2 + b ^ 2) = a * c + b * d := div_mul_cancel₀ _ hs.ne'
  · change c * k ^ 2 = xi * k ^ 2 * a + -b
    rw [hk2]; linear_combination (-a) * hx + (-b) * hdet
  · change d * k ^ 2 = xi * k ^ 2 * b + a
    rw [hk2]; linear_combination (-b) * hx + a * hdet

end X4IwOne


open scoped Matrix.Norms.Frobenius
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4IwDim

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix X4Iw X4Cayley

variable {n : ℕ}

/-- block assembly as a linear map -/
def fbL (n : ℕ) : (Sq n × Sq n) × (Sq n × Sq n) →ₗ[ℝ] Mt n where
  toFun p := fromBlocks p.1.1 p.1.2 p.2.1 p.2.2
  map_add' p q := by simp [fromBlocks_add]
  map_smul' c p := by simp [fromBlocks_smul]

lemma fb_contDiff : ContDiff ℝ 1 (fbL n) := (fbL n).toContinuousLinearMap.contDiff

def slL (n : ℕ) : Sq n →ₗ[ℝ] Sq n where
  toFun K := Matrix.of fun i j => if j < i then K i j else 0
  map_add' K L := by ext i j; simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c K := by ext i j; simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

def trL (n : ℕ) : Sq n →ₗ[ℝ] Sq n where
  toFun K := Kᵀ
  map_add' K L := transpose_add K L
  map_smul' c K := transpose_smul c K

def tlL (n : ℕ) : Mt n →ₗ[ℝ] Sq n where
  toFun N := N.toBlocks₁₁
  map_add' K L := by ext i j; simp [toBlocks₁₁]
  map_smul' c K := by ext i j; simp [toBlocks₁₁]

def blL (n : ℕ) : Mt n →ₗ[ℝ] Sq n where
  toFun N := N.toBlocks₂₁
  map_add' K L := by ext i j; simp [toBlocks₂₁]
  map_smul' c K := by ext i j; simp [toBlocks₂₁]

def diagL (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] Sq n where
  toFun κ := diagonal κ
  map_add' κ μ := (diagonal_add κ μ).symm
  map_smul' c κ := by rw [RingHom.id_apply, diagonal_smul]

lemma clm_cd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ₗ[ℝ] F) : ContDiff ℝ 1 f :=
  f.toContinuousLinearMap.contDiff

lemma ult_sl {A : Sq n} (h : ULT A) : A = 1 + slL n A := by
  ext i j
  simp only [slL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.of_apply]
  rcases lt_trichotomy j i with hij | rfl | hij
  · rw [if_pos hij, Matrix.one_apply_ne (ne_of_gt hij), zero_add]
  · rw [if_neg (lt_irrefl _), Matrix.one_apply_eq, h.1, add_zero]
  · rw [if_neg (not_lt.mpr hij.le), Matrix.one_apply_ne (ne_of_lt hij), h.2 i j hij, add_zero]

lemma ult_one_sl (K : Sq n) : ULT (1 + slL n K) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [slL]
  · simp [slL, Matrix.one_apply_ne (ne_of_lt hij), not_lt.mpr hij.le]

lemma sl_idem (K : Sq n) : slL n (slL n K) = slL n K := by
  ext i j
  simp only [slL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  split_ifs <;> rfl

lemma sl_skew {K : Sq n} (hK : Kᵀ = -K) : slL n K - (slL n K)ᵀ = K := by
  ext i j
  have hij := congrFun (congrFun hK j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
  simp only [slL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy j i with h | rfl | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le), sub_zero]
  · rw [if_neg (lt_irrefl _)]; linarith
  · rw [if_neg (not_lt.mpr h.le), if_pos h]; linarith

lemma sl_sl (A : Sq n) : slL n (slL n A - (slL n A)ᵀ) = slL n A := by
  ext i j
  simp only [slL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; exact lt_asymm h1 h2) | simp

lemma skew_mem (A : Sq n) : slL n A - (slL n A)ᵀ ∈ W (∅ : Set (Sq n)) := by
  refine ⟨?_, fun t ht => absurd ht (Set.notMem_empty t)⟩
  rw [transpose_sub, transpose_transpose, neg_sub]

abbrev E (n : ℕ) := ↥(W (∅ : Set (Sq n))) × ↥(symSub n)

lemma finrank_E (n : ℕ) : Module.finrank ℝ (E n) = n ^ 2 := by
  rw [← LinearMap.finrank_range_of_inj (blk'_inj n), range_blk', finrank_passive]

noncomputable def fpar (p : E n) : Mt n :=
  fbL n ((1 + slL n (p.1 : Sq n), 0),
    ((Ring.inverse (1 + slL n (p.1 : Sq n)))ᵀ * (p.2 : Sq n), (Ring.inverse (1 + slL n (p.1 : Sq n)))ᵀ))

lemma fpar_cd : ContDiff ℝ 1 (fpar (n := n)) := by
  have hp1 : ContDiff ℝ 1 (fun p : E n => (p.1 : Sq n)) :=
    (clm_cd (W (∅ : Set (Sq n))).subtype).comp contDiff_fst
  have hA : ContDiff ℝ 1 (fun p : E n => 1 + slL n (p.1 : Sq n)) :=
    contDiff_const.add ((clm_cd (slL n)).comp hp1)
  have hI : ContDiff ℝ 1 (fun p : E n => Ring.inverse (1 + slL n (p.1 : Sq n))) := by
    rw [contDiff_iff_contDiffAt]; intro p
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (ult_unit (ult_one_sl (n := n) p.1))
    have := contDiffAt_ringInverse ℝ (n := 1) u
    rw [hu] at this
    exact this.comp p hA.contDiffAt
  have hIt : ContDiff ℝ 1 (fun p : E n => (Ring.inverse (1 + slL n (p.1 : Sq n)))ᵀ) :=
    (clm_cd (trL n)).comp hI
  have hM : ContDiff ℝ 1 (fun p : E n => (p.2 : Sq n)) :=
    (clm_cd (symSub n).subtype).comp contDiff_snd
  exact fb_contDiff.comp ((hA.prodMk contDiff_const).prodMk ((hIt.mul hM).prodMk hIt))

def Nset (n : ℕ) : Set (Mt n) := {N | IsNilpotentFactor N}

lemma fpar_mem (p : E n) : fpar p ∈ Nset n := by
  set A := 1 + slL n (p.1 : Sq n)
  have hu := ult_one_sl (n := n) p.1
  refine ⟨A, Aᵀ⁻¹ * (p.2 : Sq n), hu.1, hu.2, ?_, ?_⟩
  · unfold Matrix.IsSymm
    rw [← Matrix.mul_assoc, ← transpose_nonsing_inv, ← transpose_mul, Matrix.nonsing_inv_mul _ (ult_unit hu),
      transpose_one, Matrix.one_mul]
    exact p.2.2
  · simp only [fpar, fbL, LinearMap.coe_mk, AddHom.coe_mk, A, ← Matrix.nonsing_inv_eq_ringInverse,
      transpose_nonsing_inv]

lemma Nset_sub : Nset n ⊆ Set.range (fpar (n := n)) := by
  rintro N ⟨A, C, h1, h2, hs, rfl⟩
  have hu : ULT A := ⟨h1, h2⟩
  refine ⟨(⟨_, skew_mem A⟩, ⟨Aᵀ * C, hs⟩), ?_⟩
  simp only [fpar, fbL, LinearMap.coe_mk, AddHom.coe_mk, sl_sl, ← ult_sl hu, ← Matrix.nonsing_inv_eq_ringInverse]
  congr 1
  rw [← Matrix.mul_assoc, ← transpose_mul, Matrix.mul_nonsing_inv _ (ult_unit hu), transpose_one,
    Matrix.one_mul]

noncomputable def gproj (N : Mt n) : Sq n × Sq n :=
  (slL n (tlL n N) - (slL n (tlL n N))ᵀ, (tlL n N)ᵀ * blL n N)

lemma gproj_cd : ContDiff ℝ 1 (gproj (n := n)) := by
  have h1 : ContDiff ℝ 1 (fun N : Mt n => slL n (tlL n N)) := (clm_cd _).comp (clm_cd _)
  exact (h1.sub ((clm_cd (trL n)).comp h1)).prodMk
    (((clm_cd (trL n)).comp (clm_cd (tlL n))).mul (clm_cd (blL n)))

def Pset (n : ℕ) : Submodule ℝ (Sq n × Sq n) := (W (∅ : Set (Sq n))).prod (symSub n)

lemma gproj_image : gproj '' Nset n = (Pset n : Set (Sq n × Sq n)) := by
  ext ⟨K, M⟩
  constructor
  · rintro ⟨N, ⟨A, C, h1, h2, hs, rfl⟩, he⟩
    simp only [gproj, tlL, blL, LinearMap.coe_mk, AddHom.coe_mk, toBlocks_fromBlocks₁₁,
      toBlocks_fromBlocks₂₁, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨skew_mem A, hs⟩
  · rintro ⟨hK, hM⟩
    refine ⟨fpar (⟨K, hK⟩, ⟨M, hM⟩), fpar_mem _, ?_⟩
    simp only [gproj, fpar, fbL, tlL, blL, LinearMap.coe_mk, AddHom.coe_mk, toBlocks_fromBlocks₁₁,
      toBlocks_fromBlocks₂₁, Prod.mk.injEq]
    have hu := ult_one_sl (n := n) K
    refine ⟨?_, ?_⟩
    · rw [map_add, show slL n 1 = 0 by ext i j; simp [slL, Matrix.one_apply]; intro h e; exact ne_of_gt h e,
        zero_add, sl_idem]
      exact sl_skew hK.1
    · rw [← Matrix.mul_assoc, ← transpose_mul, ← Matrix.nonsing_inv_eq_ringInverse,
        Matrix.nonsing_inv_mul _ (ult_unit hu), transpose_one, Matrix.one_mul]

lemma dimH_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (V : Submodule ℝ F) : dimH (V : Set F) = Module.finrank ℝ V := by
  have : (V : Set F) = ((↑) : V → F) '' Set.univ := by simp
  rw [this, isometry_subtype_coe.dimH_image, Real.dimH_univ_eq_finrank]

lemma finrank_P (n : ℕ) : Module.finrank ℝ (Pset n) = n ^ 2 := by
  have hinj : Function.Injective ((W (∅ : Set (Sq n))).subtype.prodMap (symSub n).subtype) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [LinearMap.prodMap_apply, Submodule.subtype_apply, Prod.mk.injEq] at h
    rw [Subtype.ext h.1, Subtype.ext h.2]
  rw [← finrank_E n, ← LinearMap.finrank_range_of_inj hinj, LinearMap.range_prodMap,
    Submodule.range_subtype, Submodule.range_subtype]
  rfl

theorem dimH_N : dimH (Nset n) = (n ^ 2 : ℕ) := by
  apply le_antisymm
  · calc dimH (Nset n) ≤ dimH (Set.range (fpar (n := n))) := dimH_mono Nset_sub
      _ ≤ Module.finrank ℝ (E n) := fpar_cd.dimH_range_le
      _ = (n ^ 2 : ℕ) := by rw [finrank_E]
  · calc ((n ^ 2 : ℕ) : ENNReal) = dimH (Pset n : Set (Sq n × Sq n)) := by rw [dimH_sub, finrank_P]
      _ = dimH (gproj '' Nset n) := by rw [gproj_image]
      _ ≤ dimH (Nset n) := gproj_cd.contDiffOn.dimH_image_le convex_univ (Set.subset_univ _)

def Uset (n : ℕ) : Set (Fin n → ℝ) := {κ | ∀ i, 0 < κ i}

lemma Uset_open : IsOpen (Uset n) := by
  have : Uset n = Set.pi Set.univ (fun _ => Set.Ioi 0) := by ext; simp [Uset]
  rw [this]; exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)

lemma dimH_U (n : ℕ) : dimH (Uset n) = n := by
  rw [Real.dimH_of_nonempty_interior, Module.finrank_fin_fun]
  rw [Uset_open.interior_eq]; exact ⟨fun _ => 1, fun _ => one_pos⟩

def pdL (n : ℕ) : Mt n →ₗ[ℝ] (Fin n → ℝ) where
  toFun D i := D (Sum.inl i) (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dimH_D : dimH {D : Mt n | ∃ kappa, (∀ i, 0 < kappa i) ∧ D = squeezeMatrix kappa} = n := by
  have hset : {D : Mt n | ∃ kappa, (∀ i, 0 < kappa i) ∧ D = squeezeMatrix kappa} =
      squeezeMatrix '' Uset n := by
    ext D; simp only [Set.mem_ofPred_eq, Set.mem_image, Uset]
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩, fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩⟩
  rw [hset]
  apply le_antisymm
  · have hcd : ContDiffOn ℝ 1 (squeezeMatrix (n := n)) (Uset n) := by
      intro κ hκ
      have hinv : ContDiffAt ℝ 1 (fun κ : Fin n → ℝ => fun i => (κ i)⁻¹) κ :=
        contDiffAt_pi.2 fun i => (contDiffAt_inv ℝ (hκ i).ne').comp κ (contDiff_apply ℝ ℝ i).contDiffAt
      have heq : (squeezeMatrix (n := n)) = fun κ => fbL n ((diagL n κ, 0), (0, diagL n (fun i => (κ i)⁻¹))) := by
        funext κ; rfl
      rw [heq]
      exact (fb_contDiff.contDiffAt.comp κ ((((clm_cd (diagL n)).contDiffAt).prodMk contDiffAt_const).prodMk
        (contDiffAt_const.prodMk ((clm_cd (diagL n)).contDiffAt.comp κ hinv)))).contDiffWithinAt
    have hconv : Convex ℝ (Uset n) := by
      intro x hx y hy a b ha hb hab i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases ha.lt_or_eq with ha' | rfl
      · nlinarith [hx i, hy i]
      · simp at hab; subst hab; simp [hy i]
    calc dimH (squeezeMatrix '' Uset n) ≤ dimH (Uset n) := hcd.dimH_image_le hconv subset_rfl
      _ = n := dimH_U n
  · have himg : pdL n '' (squeezeMatrix '' Uset n) = Uset n := by
      ext κ; constructor
      · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        intro i
        show 0 < (squeezeMatrix k) (Sum.inl i) (Sum.inl i)
        unfold squeezeMatrix; rw [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq]
        exact hk i
      · intro hk; exact ⟨_, ⟨κ, hk, rfl⟩, by
          ext i; show (squeezeMatrix κ) (Sum.inl i) (Sum.inl i) = κ i
          unfold squeezeMatrix; rw [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq]⟩
    calc (n : ENNReal) = dimH (Uset n) := (dimH_U n).symm
      _ = dimH (pdL n '' (squeezeMatrix '' Uset n)) := by rw [himg]
      _ ≤ _ := (clm_cd (pdL n)).contDiffOn.dimH_image_le convex_univ (Set.subset_univ _)

end X4IwDim


open scoped Matrix.Norms.Frobenius
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4IwMain

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

lemma pm_comm {K : Matrix (Phase n) (Phase n) ℝ} (h : IsPassive K) : K * sigma n = sigma n * K := by
  obtain ⟨h1, h2⟩ := h
  unfold PreservesCanonicalForm at h1
  calc K * sigma n = K * sigma n * (Kᵀ * K) := by rw [h2, Matrix.mul_one]
    _ = (K * sigma n * Kᵀ) * K := by simp only [Matrix.mul_assoc]
    _ = sigma n * K := by rw [h1]

lemma passive_of_comm {K : Matrix (Phase n) (Phase n) ℝ} (h1 : Kᵀ * K = 1)
    (h2 : K * sigma n = sigma n * K) : IsPassive K := by
  refine ⟨?_, h1⟩
  unfold PreservesCanonicalForm
  rw [h2, Matrix.mul_assoc, mul_eq_one_comm.mp h1, Matrix.mul_one]

lemma dimH_K : dimH {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} = (n ^ 2 : ℕ) := by
  have : {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} = X4Cayley.G {sigma n} := by
    ext K; constructor
    · intro h; exact ⟨h.2, fun t ht => by rw [Set.mem_singleton_iff.mp ht]; exact pm_comm h⟩
    · rintro ⟨h1, h2⟩; exact passive_of_comm h1 (h2 _ rfl)
  rw [this, X4Cayley.dimH_G]
  exact congrArg _ (X4Cayley.finrank_passive n)

end X4IwMain

open X4IwMain QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ S : Matrix (Phase n) (Phase n) ℝ, PreservesCanonicalForm S →
      ∃! f : Matrix (Phase n) (Phase n) ℝ × (Fin n → ℝ) × Matrix (Phase n) (Phase n) ℝ,
        IsNilpotentFactor f.1 ∧ (∀ i, 0 < f.2.1 i) ∧ IsPassive f.2.2 ∧
          S = f.1 * squeezeMatrix f.2.1 * f.2.2) ∧
    (∀ S : Matrix (Phase 1) (Phase 1) ℝ, PreservesCanonicalForm S →
      let a := S (Sum.inl 0) (Sum.inl 0)
      let b := S (Sum.inl 0) (Sum.inr 0)
      let c := S (Sum.inr 0) (Sum.inl 0)
      let d := S (Sum.inr 0) (Sum.inr 0)
      let xi := (a * c + b * d) / (a ^ 2 + b ^ 2)
      let eta := Real.log (a ^ 2 + b ^ 2)
      let phi := 2 * Complex.arg ((a : ℂ) - Complex.I * (b : ℂ))
      0 < a ^ 2 + b ^ 2 ∧ -2 * Real.pi < phi ∧ phi ≤ 2 * Real.pi ∧
      S = lensMatrix (fun _ _ => xi) * squeezeMatrix (fun _ => Real.exp (eta / 2)) *
        passiveMatrix (fun _ _ => Real.cos (phi / 2)) (fun _ _ => -Real.sin (phi / 2))) ∧
    dimH {N : Matrix (Phase n) (Phase n) ℝ | IsNilpotentFactor N} = (n ^ 2 : ℕ) ∧
    dimH {D : Matrix (Phase n) (Phase n) ℝ | ∃ kappa, (∀ i, 0 < kappa i) ∧ D = squeezeMatrix kappa} = n ∧
    dimH {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} = (n ^ 2 : ℕ) := by
  refine ⟨fun S hS => ?_, fun S hS => X4IwOne.one_mode S hS, X4IwDim.dimH_N, X4IwDim.dimH_D, dimH_K⟩
  obtain ⟨f, hf⟩ := X4Iw.iw_exists hS
  exact ⟨f, hf, fun g hg => X4Iw.iw_unique g f hg hf⟩

