-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.Pi_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:33:33.427889+00:00
-- url     : https://prove2.me/submissions/08599d38-b9f3-463a-ba3d-686a56023c0e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)
variable {D}
variable (D)
theorem _root_.solution (S : (n → A) →ₗ[A] (n → A)) (v : n → A) :
    D.Pi S v = D.pU v + D.pW (S (D.pW v)) := by
  first
    | (intros; simp [Dat, pU, pW, Pi])
    | (intros; unfold Dat pU pW Pi; simp)
    | (intros; simp [Dat, pU, pW, Pi]; done)
    | (intros; ext; simp [Dat, pU, pW, Pi])
    | (intros; simp only [Dat, pU, pW, Pi]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [Dat, pU, pW, Pi])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [Dat, pU, pW, Pi])
    | (intros; unfold Dat pU pW Pi; split_ifs <;> simp_all)
    | (intros; unfold Dat pU pW Pi; positivity)
    | (intros; unfold Dat pU pW Pi; ring)
    | (intros; unfold Dat pU pW Pi; exact?)
    | (intros; aesop (add norm simp [Dat, pU, pW, Pi]))
    | (intros; simp [Dat, pU, pW, Pi] <;> aesop)
    | (intros; exact Dat.symm ..)
    | (intros; exact Dat.comm ..)
    | (intros; exact pU.symm ..)
    | (intros; exact pU.comm ..)
  trace "HIT_143_2"

end 
