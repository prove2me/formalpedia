-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FiniteSections_proof_b571ce01cf9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:09.078191+00:00
-- url     : https://prove2.me/submissions/b834ea47-f066-4e7d-b419-8ba0e23f2277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tilde_eq_twist_d4135c6a21c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_secs_eq_secs_extend_88515a1497d9

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
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FiniteSections
theorem _root_.solution (hE : Extension.Statement.{u, w, w}) (hT : TildeTail.Statement.{u, w}) :
    FiniteSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q hx

  have tail : ∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (Q.twist (twistSys S x (deg j))).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (Q.twist (twistSys S x c)).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j} := by
    intro c₁
    obtain ⟨M, -, hM⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
    have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
    have hc : ∀ c : ℤ, M.tildeSys c = Q.twist (twistSys S x c) := fun c =>
      SubSystem.ext_sub fun I => by rw [← h0]; exact tilde_eq_twist M c I
    obtain ⟨n, deg, gen, hgen, hspan⟩ := hT S Ω N x M hx c₁
    refine ⟨n, deg, gen, fun j => ⟨(hgen j).1, ?_⟩, fun c hc₁ => ?_⟩
    · rw [← hc]; exact (hgen j).2
    · rw [← hc]; exact hspan c hc₁
  refine ⟨?_, tail, fun F _ _ _ _ _ => span_secs_eq_secs_extend Q.toSubSystem⟩

  obtain ⟨n, deg, gen, hgen, hspan⟩ := tail 0
  have hle : Q.secs ≤ Submodule.span S (Set.range gen) := by
    have h := hspan 0 le_rfl
    rw [SubSystem.twist_twistSys_zero] at h
    refine h.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨j, f, e, hf, hej, rfl⟩
    have he : e = 0 := by have := (hgen j).1; omega
    subst he
    have hfC : f = C (coeff 0 f) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hf.totalDegree_le)
    rw [hfC, aeval_C, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have := isNoetherian_span_of_finite S (Set.finite_range gen)
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)
end FiniteSections
end GroundTheory.Heights₂.Heights.Kleiman
