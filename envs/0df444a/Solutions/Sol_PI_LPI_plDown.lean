-- Prove2me | solution 1 for PI.LPI.plDown
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:22.43886+00:00
-- url     : https://prove2.me/submissions/f5c0cda9-52ce-4412-86db-031e5fd13143

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVMemTensInt
import Theorems.Thm_PI_LPI_prV_mem_tensInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
noncomputable section
open PI PI.LPI
namespace PI.LPI
theorem _root_.solution : PLDown := by
  intro F E _ _ _ _ _ n Lb v y hy
  have hy' : y ∈ Submodule.span (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
      ((fun x : Fin n → E => fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ''
        (Lb : Set (Fin n → E))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨l, hl, rfl⟩
  | zero =>
    convert (latV v Lb).zero_mem using 1
    funext j
    simp
  | add x y _ _ hx hy =>
    have h : (fun j => prV (E := E) v ((x + y) j)) =
        (fun j => prV (E := E) v (x j)) + (fun j => prV (E := E) v (y j)) := by
      funext j; simp
    rw [h]
    exact add_mem hx hy
  | smul s x _ hx =>
    have h : (fun j => prV (E := E) v ((s • x) j)) =
        (⟨prV (E := E) v s, prV_mem_tensInt (E := E) v s s.2⟩ :
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) •
          (fun j => prV (E := E) v (x j)) := by
      funext j
      show prV (E := E) v ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * x j) = prV (E := E) v s * prV (E := E) v (x j)
      exact map_mul _ _ _
    rw [h]
    exact Submodule.smul_mem _ _ hx
end PI.LPI
