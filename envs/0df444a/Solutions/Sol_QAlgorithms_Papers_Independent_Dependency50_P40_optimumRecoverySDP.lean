-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.optimumRecoverySDP
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:23:32.022984+00:00
-- url     : https://prove2.me/submissions/9a0bdd9f-4a69-4fd9-b0bc-ef5bc2b4a5e9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_choiChannelCorrespondence
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_recoveryTraceObjective

noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P40
open scoped ComplexConjugate ComplexOrder Matrix
open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

namespace QAlgorithms.Papers.Independent.Dependency50.P40.RecoveryCompactProof

/- The following three generic helpers are reused from fizzyinc3's accepted
optimumEncodingSDP submission 2ac1b04c-f940-405c-b5c2-f758e295b4e0,
lines112–180. Names/namespace and one deprecated simp-lemma spelling are updated. Their h is input dimension and k
is output dimension; recovery below uses h := k and k := h. -/
lemma entry_bound {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) (hX : ChoiFeasible X) (p q : Fin k × Fin h) :
    ‖X p q‖ ≤ h := by
  obtain ⟨N, A, rfl⟩ :=
    ((choiChannelCorrespondence hh hk (fun _ : Fin 0 => (0 : Matrix (Fin k) (Fin h) ℂ))).2.2.2.2.1
      X).mp hX.1
  set S : Fin k × Fin h → ℝ := fun p => ∑ j, ‖A j p.1 p.2‖ ^ 2 with hS
  have hent : ∀ p q, krausChoi A p q = ∑ j, A j p.1 p.2 * conj (A j q.1 q.2) := by
    intro p q
    simp [krausChoi, dyad, operatorKet, Matrix.sum_apply]
  have hsum : ∑ p, S p = h := by
    have h1 : ∀ u, ∑ x, krausChoi A (x, u) (x, u) = 1 := by
      intro u
      have := congrFun (congrFun hX.2 u) u
      simpa [traceLeft] using this
    have h2 : ∑ p, ((S p : ℝ) : ℂ) = ∑ p, krausChoi A p p := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hent, hS]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have h3 : ∑ p, krausChoi A p p = h := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [h1]
    have : ((∑ p, S p : ℝ) : ℂ) = (h : ℂ) := by push_cast; rw [h2, h3]
    exact_mod_cast this
  have hSn : ∀ p, 0 ≤ S p := fun p => Finset.sum_nonneg fun j _ => by positivity
  have hSle : ∀ p, S p ≤ h := by
    intro p
    rw [← hsum]
    exact Finset.single_le_sum (fun p _ => hSn p) (Finset.mem_univ p)
  rw [hent]
  calc ‖∑ j, A j p.1 p.2 * conj (A j q.1 q.2)‖
      ≤ ∑ j, ‖A j p.1 p.2 * conj (A j q.1 q.2)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖A j p.1 p.2‖ ^ 2 + ‖A j q.1 q.2‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖A j p.1 p.2‖ - ‖A j q.1 q.2‖)]
    _ = (S p + S q) / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ h := by linarith [hSle p, hSle q]

lemma isClosed_feasible {h k : ℕ} :
    IsClosed {X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ | ChoiFeasible X} := by
  have e : {X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ | ChoiFeasible X} =
      {X | Xᴴ = X} ∩ (⋂ x : Fin k × Fin h → ℂ, {X | 0 ≤ star x ⬝ᵥ X *ᵥ x}) ∩
        {X | traceLeft X = 1} := by
    ext X
    simp only [ChoiFeasible, Matrix.posSemidef_iff_dotProduct_mulVec, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_iInter, Matrix.IsHermitian, and_assoc]
  rw [e]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_eq (by fun_prop) continuous_id
  · refine isClosed_iInter fun x => ?_
    exact isClosed_le continuous_const (by fun_prop)
  · refine isClosed_eq ?_ continuous_const
    unfold traceLeft
    fun_prop

lemma isCompact_feasible {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    IsCompact {X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ | ChoiFeasible X} := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin k × Fin h =>
      Set.univ.pi fun _ : Fin k × Fin h => Metric.closedBall (0 : ℂ) h) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset isClosed_feasible ?_
  intro X hX
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun p q => entry_bound hh hk X hX p q


end QAlgorithms.Papers.Independent.Dependency50.P40.RecoveryCompactProof

theorem solution {h k a m : ℕ} (hh : 0 < h) (hk : 0 < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (hE : IsKrausFamily E) :
    (∀ R : Superop (Fin k) (Fin h), IsChannel R →
      ChoiFeasible (outputFirstChoi R) ∧ purificationFidelity psi (R ∘ krausApply E) =
        (outputFirstChoi R * recoveryCoefficient rho E).trace.re) ∧
    (∀ X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ, ChoiFeasible X →
      ∃ R : Superop (Fin k) (Fin h), IsChannel R ∧ outputFirstChoi R = X) ∧
    ∃ (R : Superop (Fin k) (Fin h))
      (X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ),
      IsChannel R ∧ outputFirstChoi R = X ∧ ChoiFeasible X ∧
      purificationFidelity psi (R ∘ krausApply E) =
        (X * recoveryCoefficient rho E).trace.re ∧
      (∀ Y, ChoiFeasible Y → (Y * recoveryCoefficient rho E).trace.re ≤
        (X * recoveryCoefficient rho E).trace.re) ∧
      (∀ S : Superop (Fin k) (Fin h), IsChannel S →
        purificationFidelity psi (S ∘ krausApply E) ≤
          purificationFidelity psi (R ∘ krausApply E)) := by
  have C := choiChannelCorrespondence hk hh
    (fun _ : Fin 0 => (0 : Matrix (Fin h) (Fin k) ℂ))
  have P1 : ∀ R : Superop (Fin k) (Fin h), IsChannel R →
      ChoiFeasible (outputFirstChoi R) ∧
      purificationFidelity psi (R ∘ krausApply E) =
        (outputFirstChoi R * recoveryCoefficient rho E).trace.re := by
    intro R hR
    refine ⟨?_, (recoveryTraceObjective hh hk rho hrho psi hpsi E hE R hR).2.2⟩
    rw [C.2.2.2.2.2.1, C.2.2.2.2.2.2.2 R hR]
    exact hR
  have P2 : ∀ X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ, ChoiFeasible X →
      ∃ R : Superop (Fin k) (Fin h), IsChannel R ∧ outputFirstChoi R = X :=
    fun X hX => ⟨fromOutputFirstChoi X, (C.2.2.2.2.2.1 X).mp hX,
      C.2.2.2.2.2.2.1 X⟩
  refine ⟨P1, P2, ?_⟩
  have hne : ({X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ |
      ChoiFeasible X}).Nonempty := by
    refine ⟨((h : ℂ)⁻¹) • 1, ?_, ?_⟩
    · exact Matrix.PosSemidef.one.smul (by
        have : (0 : ℝ) ≤ (h : ℝ)⁻¹ := by positivity
        have h2 := Complex.zero_le_real.mpr this
        simp_all)
    · ext u v
      by_cases huv : u = v
      · subst huv
        simp [traceLeft, Matrix.one_apply]
        field_simp
      · simp [traceLeft, Matrix.one_apply, huv]
  obtain ⟨X, hX, hmax⟩ :=
    (RecoveryCompactProof.isCompact_feasible hk hh).exists_isMaxOn hne
      (Continuous.continuousOn (f := fun Y : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ =>
        (Y * recoveryCoefficient rho E).trace.re) (by fun_prop))
  obtain ⟨R, hR, hRX⟩ := P2 X hX
  refine ⟨R, X, hR, hRX, hX, ?_, ?_, ?_⟩
  · rw [(P1 R hR).2, hRX]
  · intro Y hY
    exact hmax hY
  · intro S hS
    rw [(P1 R hR).2, (P1 S hS).2, hRX]
    exact hmax (P1 S hS).1

end
