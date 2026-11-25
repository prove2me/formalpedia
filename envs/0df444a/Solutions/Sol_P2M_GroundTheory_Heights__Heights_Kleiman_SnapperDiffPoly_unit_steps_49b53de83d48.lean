-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_unit_steps_49b53de83d48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:16.50135+00:00
-- url     : https://prove2.me/submissions/b8e42f1a-3d44-4eab-81a5-6b997045e80f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_succ_a74d7db17473
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_update_db7c32974b5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_exists_fwd_antideriv_18f66ff8e357
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
theorem _root_.solution {t D : ℕ} (g : (Fin t → ℕ) → ℤ → ℚ)
    (hc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c))
    (hj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c)) :
    IsNumPolyLT t (D + 1) g := by
  classical
  obtain ⟨Qc, hQc, hcE⟩ := hc
  choose Q hQ hjE using hj
  obtain ⟨Pc, hPcd, hPc⟩ := exists_fwd_antideriv D (Fin.last t) Qc hQc
  choose P hPd hP using fun j : Fin t => exists_fwd_antideriv D j.castSucc (Q j) (hQ j)

  have hcol : ∀ c : ℤ, g 0 c - g 0 0 = eval (numPt 0 c) Pc - eval (numPt 0 0) Pc := by
    have step : ∀ c : ℤ, g 0 (c + 1) - g 0 c = eval (numPt 0 (c + 1)) Pc - eval (numPt 0 c) Pc := by
      intro c
      have h1 : g 0 (c + 1) - g 0 c = eval (numPt 0 c) Qc := hcE 0 c
      rw [h1, numPt_succ, hPc]
    intro c
    induction c using Int.induction_on with
    | zero => simp
    | succ i ih => have := step i; linarith
    | pred i ih =>
      have := step (-(i : ℤ) - 1)
      rw [sub_add_cancel] at this
      linarith

  have hrow : ∀ (i : Fin t) (v : Fin t → ℕ) (c : ℤ) (m : ℕ),
      g (Function.update v i m) c - g (Function.update v i 0) c =
        eval (numPt (Function.update v i m) c) (P i) - eval (numPt (Function.update v i 0) c) (P i) := by
    intro i v c m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : g (Function.update (Function.update v i m) i (Function.update v i m i + 1)) c -
          g (Function.update v i m) c = eval (numPt (Function.update v i m) c) (Q i) := hjE i _ c
      have h2 := hP i (numPt (Function.update v i m) c)
      rw [← numPt_update] at h2
      simp only [Function.update_self, Function.update_idem] at h1 h2
      linarith

  let tr : Finset (Fin t) → (Fin t → ℕ) → (Fin t → ℕ) := fun s n i => if i ∈ s then n i else 0
  let σ : Finset (Fin t) → Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ := fun s =>
    Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => if i ∈ s then X i.castSucc else 0)
      (X (Fin.last t))
  have hσd : ∀ s k, (σ s k).totalDegree ≤ 1 := by
    intro s k
    induction k using Fin.lastCases with
    | last => simp [σ, totalDegree_X]
    | cast i => simp only [σ, Fin.snoc_castSucc]; split_ifs <;> simp [totalDegree_X]
  have hσe : ∀ s n c, (fun k => eval (numPt n c) (σ s k)) = numPt (tr s n) c := by
    intro s n c
    funext k
    induction k using Fin.lastCases with
    | last => simp [σ, numPt]
    | cast i => simp only [σ, tr, numPt, Fin.snoc_castSucc]; split_ifs <;> simp
  have key : ∀ s : Finset (Fin t), ∃ Γ : MvPolynomial (Fin (t + 1)) ℚ, Γ.totalDegree ≤ D ∧
      ∀ n c, g (tr s n) c = eval (numPt n c) Γ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨aeval (σ ∅) Pc + C (g 0 0 - eval (numPt 0 0) Pc), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; exact Nat.zero_le _))
        exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd ∅) _).trans hPcd
      · have h0 : tr ∅ n = 0 := by funext i; simp [tr]
        rw [map_add, eval_C, eval_aeval_eq, hσe, h0]
        linarith [hcol c]
    | insert i s hi ih =>
      obtain ⟨Γ, hΓd, hΓ⟩ := ih
      refine ⟨Γ + (aeval (σ (insert i s)) (P i) - aeval (σ s) (P i)), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le hΓd ((totalDegree_sub _ _).trans (max_le ?_ ?_)))
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
      · have e1 : tr (insert i s) n = Function.update (tr s n) i (n i) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr]
          · simp [tr, hk]
        have e2 : tr s n = Function.update (tr s n) i 0 := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr, hi]
          · simp [hk]
        have h := hrow i (tr s n) c (n i)
        rw [← e1, ← e2] at h
        rw [map_add, map_sub, eval_aeval_eq, eval_aeval_eq, hσe, hσe, ← hΓ n c]
        linarith
  obtain ⟨Γ, hΓd, hΓ⟩ := key Finset.univ
  refine ⟨Γ, Or.inr (by omega), fun n c => ?_⟩
  have h := hΓ n c
  have hu : tr Finset.univ n = n := by funext i; simp [tr]
  rw [hu] at h
  exact h
end GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
