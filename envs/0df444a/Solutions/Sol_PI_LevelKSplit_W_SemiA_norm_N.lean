-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.norm_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:58.50434+00:00
-- url     : https://prove2.me/submissions/31fcd02a-2cb7-4240-8e8c-1a04e35b6c03

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution {h n : HA R σ J} (hh : h ∈ Hsub R σ J P) (hn : n ∈ Nsub R σ J P) :
    h * n * h⁻¹ ∈ Nsub R σ J P := by
  have hfix : ∀ b, lin R σ J h (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := by
    intro b
    have hh' := hh
    unfold Hsub stabT tupH at hh'
    rw [MulAction.mem_stabilizer_iff] at hh'
    have := congrFun hh' (Fin.castAdd r (Fin.castSucc b))
    unfold ratTup at this
    change lin R σ J h (ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r (Fin.castSucc b)))) =
      ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r (Fin.castSucc b))) at this
    rw [Fin.append_left] at this
    simpa [F0, Fin.snoc_castSucc] using this
  have huni : h ∈ uniFlag R σ J P.e := by
    show UniC R σ J P.e h
    intro b
    rw [hfix b, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨hn1, hn2⟩ := hn
  refine ⟨?_, fun v hv => ?_⟩
  · exact (uniFlag R σ J P.e).mul_mem ((uniFlag R σ J P.e).mul_mem huni hn1)
      ((uniFlag R σ J P.e).inv_mem huni)
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      rw [← hR_lin h, lin_lin_inv, hfix a]
      exact hv a
    have h1 := hn2 _ hu
    have h2 : lin R σ J h (lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v) ∈
        spanR (F := F) R P.e Set.univ :=
      uni_map_le huni Set.univ (fun _ _ _ _ => Set.mem_univ _) (Submodule.mem_map_of_mem h1)
    rw [map_sub, lin_lin_inv] at h2
    rw [lin_mul, lin_mul]
    simpa using h2
end PI.LevelKSplit.W.SemiA
