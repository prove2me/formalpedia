-- Prove2me | solution 1 for SemilinearHJ.Verification.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:37:16.205746+00:00
-- url     : https://prove2.me/submissions/b6bb278a-8d35-4fe4-9f55-687eda743a8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting
import Theorems.Thm_SemilinearHJ_Verification_theorem_4_2
import Theorems.Thm_SemilinearHJ_Verification_eq_4_7
import Theorems.Thm_SemilinearHJ_Verification_viscSub_imp_aeSubsol
import Theorems.Thm_SemilinearHJ_Verification_aeSubsol_imp_viscSub

open SemilinearHJ.Verification
open scoped ENNReal MeasureTheory

/-- `H(x, u) ≥ 0` at states where `Ψ(x) ≥ 0`: the choice `v = 0 ∈ TX ∩ B_r` gives value `0`. -/
lemma ham_nonneg_aux {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (hr : 0 < r) (x u : E n)
    (hΨx : ∀ i, 0 ≤ Ψ x i) : 0 ≤ ham X Ψ r x u := by
  unfold ham
  have h0 : (0 : E n) ∈ ballR X r := ⟨Submodule.zero_mem _, by simp [l1, hr.le]⟩
  have hbdd : BddAbove ((fun v => inner ℝ u v - ∑ i, Ψ x i * max (v i) 0) '' ballR X r) := by
    refine ⟨r * ∑ i, |u i|, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hvi : ∀ i, |v i| ≤ r := fun i =>
      le_trans (Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)) hv.2
    have h1 : inner ℝ u v ≤ r * ∑ i, |u i| := by
      rw [PiLp.inner_apply, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [RCLike.inner_apply, conj_trivial]
      calc v i * u i ≤ |v i * u i| := le_abs_self _
        _ = |v i| * |u i| := abs_mul _ _
        _ ≤ r * |u i| := mul_le_mul_of_nonneg_right (hvi i) (abs_nonneg _)
    have h2 : 0 ≤ ∑ i, Ψ x i * max (v i) 0 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hΨx i) (le_max_right _ _)
    linarith
  refine le_trans ?_ (le_csSup hbdd ⟨0, h0, rfl⟩)
  simp

theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    (∀ x ∈ X, srcVal X Ψ r X0 x ≠ ⊤) ∧
      (∃ K : NNReal, LipschitzOnWith K (fun x => (srcVal X Ψ r X0 x).toReal) X) ∧
      AESubsol X Ψ r (fun x => (srcVal X Ψ r X0 x).toReal) ∧
      (∀ x ∈ X0, (srcVal X Ψ r X0 x).toReal = 0) ∧
      ∀ V' : E n → ℝ, (∃ K : NNReal, LipschitzOnWith K V' X) → AESubsol X Ψ r V' →
        (∀ x ∈ X0, V' x = 0) → ∀ x ∈ X, V' x ≤ (srcVal X Ψ r X0 x).toReal := by
  obtain ⟨hfin, hmaxsol, -⟩ := theorem_4_2 X hX Ψ hΨL hΨ0 r hr X0 hX0c hX0X hX0
  obtain ⟨hsol, hmax⟩ := hmaxsol
  have hLip := (eq_4_7 X hX Ψ hΨL hΨ0 r hr X0 hX0c hX0X _ hsol).1
  refine ⟨hfin, hLip, viscSub_imp_aeSubsol X hX Ψ hΨL hΨ0 r hr X0 hX0c hX0X _ hLip hsol.1,
    hsol.1.2.1, ?_⟩
  intro V' hV'L hV'sub hV'0
  have hsub' := aeSubsol_imp_viscSub X hX Ψ hΨL hΨ0 r hr X0 hX0c hX0X V' hV'L hV'sub hV'0
  -- the supersolution test is vacuous since `H ≥ 0`
  have hsuper : IsViscSuper X Ψ r X0 V' :=
    ⟨hsub'.1, hV'0, fun ϕ _ x0 hx0 _ => ham_nonneg_aux X Ψ r hr x0 _ (hΨ0 x0 hx0.1)⟩
  exact hmax V' ⟨hsub', hsuper⟩
