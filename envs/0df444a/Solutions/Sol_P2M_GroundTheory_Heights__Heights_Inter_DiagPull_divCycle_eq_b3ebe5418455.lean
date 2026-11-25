-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_divCycle_eq_b3ebe5418455
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:04.557778+00:00
-- url     : https://prove2.me/submissions/921b78da-4101-42b8-8556-01146baabb52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_mem_minimalPrimes_of_cross_a4bf0f01ea5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_locLen_cross_60ec489fea52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_cross_mem_0576bce22251
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_notMem_25089793c224
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multAt_eq_locLen_edc0f73897e5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution (s : MRing (T.yyIdx ι ν κ)) (d : T.YBlk → ℕ) (hs : IsMultiHomog s d) :
    divCycle (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 0) s) =
      divCycle (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 1) s) := by
  classical
  have hV : (T.wwIdeal x δ e φ a₀ a₀).IsPrime := RingHom.ker_isPrime _
  have hc := cross_mem x δ e φ a₀ s d hs
  have hc' : ∀ k : κ, rename (T.yyEmb 1) s * X ⟨.line0, k⟩ ^ d .line -
      rename (T.yyEmb 0) s * X ⟨.line1, k⟩ ^ d .line ∈ T.wwIdeal x δ e φ a₀ a₀ := fun k => by
    rw [← neg_sub]
    exact neg_mem (hc k)
  have hsupp : ∀ W, W ∈ divSupp (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 0) s) ↔
      W ∈ divSupp (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 1) s) := by
    intro W
    constructor
    · rintro ⟨hW, hr⟩
      obtain ⟨k, h0, h1⟩ := exists_line_notMem x δ e φ a₀ hW.1.1 (le_sup_left.trans hW.1.2) hr
      exact ⟨mem_minimalPrimes_of_cross (hc k) hW (fun h => h0 (hW.1.1.mem_of_pow_mem _ h))
        (fun h => h1 (hW.1.1.mem_of_pow_mem _ h)), hr⟩
    · rintro ⟨hW, hr⟩
      obtain ⟨k, h0, h1⟩ := exists_line_notMem x δ e φ a₀ hW.1.1 (le_sup_left.trans hW.1.2) hr
      exact ⟨mem_minimalPrimes_of_cross (hc' k) hW (fun h => h1 (hW.1.1.mem_of_pow_mem _ h))
        (fun h => h0 (hW.1.1.mem_of_pow_mem _ h)), hr⟩
  ext W
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 0) s)
  · rw [if_pos h, if_pos ((hsupp W).1 h)]
    obtain ⟨hW, hr⟩ := h
    have hWp := hW.1.1
    obtain ⟨k, h0, h1⟩ := exists_line_notMem x δ e φ a₀ hWp (le_sup_left.trans hW.1.2) hr
    rw [multAt_eq_locLen _ _ hWp, multAt_eq_locLen _ _ hWp,
      locLen_cross hV (hc k) ⟨W, hWp⟩ (le_sup_left.trans hW.1.2)
        (fun h => h0 (hWp.mem_of_pow_mem _ h)) (fun h => h1 (hWp.mem_of_pow_mem _ h))]
  · rw [if_neg h, if_neg (mt (hsupp W).2 h)]
end GroundTheory.Heights₂.Heights.Inter.DiagPull
