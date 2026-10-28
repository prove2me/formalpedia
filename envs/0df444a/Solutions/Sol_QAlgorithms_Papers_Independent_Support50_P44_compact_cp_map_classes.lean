-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P44.compact_cp_map_classes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:18:52.686995+00:00
-- url     : https://prove2.me/submissions/84fa297f-db33-408d-87f5-b3700ae4ad67

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

open scoped Matrix ComplexOrder ComplexConjugate

namespace X7cs

theorem closed_psd {E : Type*} [Fintype E] :
    IsClosed {X : Matrix E E ℂ | X.PosSemidef} := by
  have e : {X : Matrix E E ℂ | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ x : E → ℂ, {X | 0 ≤ (star x ⬝ᵥ (X *ᵥ x)).re ∧ (star x ⬝ᵥ (X *ᵥ x)).im = 0} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec,
      Matrix.IsHermitian, Complex.nonneg_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
  rw [e]
  refine IsClosed.inter (isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id) ?_
  refine isClosed_iInter fun x => ?_
  have hc : Continuous fun X : Matrix E E ℂ => star x ⬝ᵥ (X *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  exact IsClosed.inter (isClosed_le continuous_const (Complex.continuous_re.comp hc))
    (isClosed_eq (Complex.continuous_im.comp hc) continuous_const)

theorem entry_bound {E : Type*} [Fintype E] [DecidableEq E] (X : Matrix E E ℂ) (hX : X.PosSemidef) (i j : E) :
    ‖X i j‖ ≤ X.trace.re := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  have hent : ∀ a b, X a b = ∑ k, v k a * conj (v k b) := by
    intro a b; rw [hv, Matrix.sum_apply]; simp [Matrix.vecMulVec_apply]
  have htr : X.trace.re = ∑ k, ∑ a, Complex.normSq (v k a) := by
    rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.diag, hent, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [hent, htr]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖v k i‖ * ‖v k j‖ ≤ (Complex.normSq (v k i) + Complex.normSq (v k j)) / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖v k i‖ - ‖v k j‖)]
  by_cases hij : i = j
  · subst hij
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have := Finset.sum_nonneg (s := Finset.univ.erase i) fun a _ => Complex.normSq_nonneg (v k a)
    linarith
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    have := Finset.sum_nonneg (s := (Finset.univ.erase i).erase j) fun a _ => Complex.normSq_nonneg (v k a)
    have h2 := Complex.normSq_nonneg (v k i)
    have h3 := Complex.normSq_nonneg (v k j)
    linarith

theorem main {E : Type*} [Fintype E] [DecidableEq E] (alpha : ℝ) (halpha : 0 ≤ alpha) :
    IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re ≤ alpha} ∧
      IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re = alpha} := by
  have hK : IsCompact (Set.univ.pi fun _ : E => Set.univ.pi fun _ : E => Metric.closedBall (0 : ℂ) alpha) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 alpha
  have htr : Continuous fun X : Matrix E E ℂ => X.trace.re := by
    simp only [Matrix.trace, Matrix.diag]; fun_prop
  have h1 : IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re ≤ alpha} := by
    refine hK.of_isClosed_subset ?_ ?_
    · exact IsClosed.inter closed_psd (isClosed_le htr continuous_const)
    · rintro X ⟨hX, ht⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
      intro i j
      exact (entry_bound X hX i j).trans ht
  refine ⟨h1, h1.of_isClosed_subset ?_ ?_⟩
  · exact IsClosed.inter closed_psd (isClosed_eq htr continuous_const)
  · rintro X ⟨hX, ht⟩; exact ⟨hX, ht.le⟩

end X7cs

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open scoped Matrix ComplexOrder

def X7cs_inv {E G : Type*} [Fintype E] (C : Matrix (E × G) (E × G) ℂ) :
    Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ where
  toFun X := Matrix.of fun a b => ∑ i, ∑ j, X i j * C (i, a) (j, b)
  map_add' X Y := by
    ext a b; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b; simp [Finset.mul_sum, mul_assoc]

theorem X7cs_map_inv {E G : Type*} [Fintype E] [DecidableEq E] (C : Matrix (E × G) (E × G) ℂ) :
    mapChoi (X7cs_inv C) = C := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [mapChoi, X7cs_inv, Matrix.single_apply, ite_and]

theorem X7cs_inv_map {E G : Type*} [Fintype E] [DecidableEq E] (Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ) :
    X7cs_inv (mapChoi Phi) = Phi := by
  apply LinearMap.ext; intro X
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  have hs : ∀ i j, Matrix.single i j (X i j) = X i j • (Matrix.single i j 1 : Matrix E E ℂ) := by
    intro i j; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [hs, map_sum, map_smul]
  ext a b
  simp only [X7cs_inv, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, mapChoi, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

theorem X7cs_tr_inv {E G : Type*} [Fintype E] [Fintype G] [DecidableEq E]
    (C : Matrix (E × G) (E × G) ℂ) (i : E) :
    (X7cs_inv C (Matrix.single i i 1)).trace = ∑ a, C (i, a) (i, a) := by
  simp [X7cs_inv, Matrix.trace, Matrix.single_apply, ite_and]

theorem X7cs_tr {E G : Type*} [Fintype E] [Fintype G] [DecidableEq E]
    (C : Matrix (E × G) (E × G) ℂ) :
    C.trace = ∑ i, (X7cs_inv C (Matrix.single i i 1)).trace := by
  rw [Finset.sum_congr rfl fun i _ => X7cs_tr_inv C i]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

theorem X7cs_single_psd {E : Type*} [Fintype E] [DecidableEq E] (i : E) :
    (Matrix.single i i (1 : ℂ)).PosSemidef := by
  have : Matrix.single i i (1 : ℂ) = Matrix.diagonal (Pi.single i 1) := by
    ext a b; simp [Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply]; aesop
  rw [this]
  refine Matrix.PosSemidef.diagonal fun a => ?_
  by_cases h : a = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem X7cs_cont {E G : Type*} [Fintype E] [Fintype G] (X : Matrix E E ℂ) :
    Continuous fun C : Matrix (E × G) (E × G) ℂ => (X7cs_inv C X).trace := by
  simp only [X7cs_inv, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace, Matrix.diag, Matrix.of_apply]
  fun_prop

theorem X7cs_cpmain {E G : Type*} [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G] :
    letI := finiteMapTopology (E := E) (G := G)
    IsCompact {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTNI Phi} ∧
    IsCompact {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTP Phi} := by
  letI := finiteMapTopology (E := E) (G := G)
  have hind : Topology.IsInducing (mapChoi (E := E) (G := G)) := ⟨rfl⟩
  have hK := (X7cs.main (E := E × G) (Fintype.card E : ℝ) (by positivity)).1
  constructor
  · rw [hind.isCompact_iff]
    have e : mapChoi '' {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTNI Phi} =
        {C | C.PosSemidef} ∩ ⋂ X : Matrix E E ℂ, ⋂ (_ : X.PosSemidef),
          {C | (X7cs_inv C X).trace.re ≤ X.trace.re} := by
      ext C
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨Phi, ⟨h1, h2⟩, rfl⟩
        exact ⟨h1, by rw [X7cs_inv_map]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨X7cs_inv C, ⟨by unfold FiniteCP; rw [X7cs_map_inv]; exact h1, h2⟩, X7cs_map_inv C⟩
    rw [e]
    refine hK.of_isClosed_subset ?_ ?_
    · refine IsClosed.inter X7cs.closed_psd ?_
      exact isClosed_iInter fun X => isClosed_iInter fun _ =>
          isClosed_le (Complex.continuous_re.comp (X7cs_cont X)) continuous_const
    · rintro C ⟨h1, h2⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at h2 h1
      refine ⟨h1, ?_⟩
      rw [X7cs_tr, Complex.re_sum]
      calc ∑ i, (X7cs_inv C (Matrix.single i i 1)).trace.re ≤ ∑ i : E, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => by
              have := h2 _ (X7cs_single_psd i)
              simpa [Matrix.trace, Matrix.single_apply] using this
        _ = Fintype.card E := by simp
  · rw [hind.isCompact_iff]
    have e : mapChoi '' {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTP Phi} =
        {C | C.PosSemidef} ∩ ⋂ X : Matrix E E ℂ, {C | (X7cs_inv C X).trace = X.trace} := by
      ext C
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨Phi, ⟨h1, h2⟩, rfl⟩
        exact ⟨h1, by rw [X7cs_inv_map]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨X7cs_inv C, ⟨by unfold FiniteCP; rw [X7cs_map_inv]; exact h1, h2⟩, X7cs_map_inv C⟩
    rw [e]
    refine hK.of_isClosed_subset ?_ ?_
    · refine IsClosed.inter X7cs.closed_psd ?_
      exact isClosed_iInter fun X => isClosed_eq (X7cs_cont X) continuous_const
    · rintro C ⟨h1, h2⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at h2 h1
      refine ⟨h1, le_of_eq ?_⟩
      rw [X7cs_tr, Complex.re_sum]
      simp only [h2]
      simp [Matrix.trace, Matrix.single_apply]

end QAlgorithms.Papers.Independent.Support50.P44

end

open QAlgorithms.Papers.Independent.Support50.P44 in
theorem solution {E G : Type*} [Fintype E] [Fintype G]
    [DecidableEq E] [DecidableEq G] :
    letI := finiteMapTopology (E := E) (G := G)
    IsCompact {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTNI Phi} ∧
    IsCompact {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTP Phi} :=
  X7cs_cpmain
