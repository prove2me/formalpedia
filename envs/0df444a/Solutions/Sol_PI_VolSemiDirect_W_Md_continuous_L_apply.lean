-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_L_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:04.380454+00:00
-- url     : https://prove2.me/submissions/85536306-1cad-41f8-aeff-3883f0f3dd9b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_hR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Md
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable [IsTopologicalRing (R ⊗[F] E)]
namespace PI.VolSemiDirect.W.Md
theorem _root_.solution {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => (datR R σ J P T).L (w x) (s x) v := by
  set D := datR R σ J P T with hD
  have key : (fun x => D.L (w x) (s x) v) = fun x =>
      v + ∑ b, D.hL (D.e b) v • (w x b + ∑ a, s x a b • D.e a) - ∑ a, D.hL (w x a) (D.pW v) • D.e a := by
    funext x
    simp only [PI.VolSemiDirect.W.PG.Dat.L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]
  rw [key]
  have hh : ∀ (c : Fin M → R ⊗[F] E), Continuous fun u : Fin M → R ⊗[F] E => D.hL u c := by
    intro c
    first
      | exact continuous_hR R σ J (u := fun u => u) (v := fun _ => c) continuous_id continuous_const
      | exact continuous_hR R σ J (u := fun _ => c) (v := fun u => u) continuous_const continuous_id
  have hA : ∀ b : Fin r, Continuous fun x => w x b + ∑ a, s x a b • D.e a := by
    intro b
    have h1 : Continuous fun x => w x b := (continuous_apply b).comp hw
    have h2 : ∀ a : Fin r, Continuous fun x => s x a b • D.e a := by
      intro a
      have h3 : Continuous fun x => s x a b := (continuous_apply b).comp ((continuous_apply a).comp hs)
      exact h3.smul continuous_const
    exact h1.add (continuous_finset_sum _ fun a _ => h2 a)
  have hB : ∀ b : Fin r, Continuous fun x => D.hL (D.e b) v • (w x b + ∑ a, s x a b • D.e a) := by
    intro b
    exact (continuous_const (y := D.hL (D.e b) v)).smul (hA b)
  have hC : ∀ a : Fin r, Continuous fun x => D.hL (w x a) (D.pW v) • D.e a := by
    intro a
    have h4 : Continuous fun x => D.hL (w x a) (D.pW v) := (hh (D.pW v)).comp ((continuous_apply a).comp hw)
    exact h4.smul continuous_const
  exact (continuous_const.add (continuous_finset_sum _ fun b _ => hB b)).sub
    (continuous_finset_sum _ fun a _ => hC a)
end PI.VolSemiDirect.W.Md
