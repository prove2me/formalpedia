-- Prove2me | solution 1 for TarchaBraids.permutation_correction_to_kernel_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T04:33:22.712022+00:00
-- url     : https://prove2.me/submissions/3719d945-e342-41f0-b8fe-bd1104f63702

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ)
    (hp : IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n)))
    (hgen : ∀ i : Fin (n - 1),
      hp.fundamentalGroupToMulOpposite
        (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})
        (halfTwistBraid n i) =
      MulOpposite.op (Equiv.swap (strandIdx i) (strandIdxSucc i)))
    (hswap : Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) =>
        Equiv.swap (strandIdx i) (strandIdxSucc i))))
    (β : GeomBraidGroup n) :
    ∃ w : FreeGroup (Fin (n - 1)),
      β * (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w)⁻¹ ∈
        (hp.fundamentalGroupToMulOpposite
          (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})).ker := by
  let e : (configProj n) ⁻¹' {baseUnordered n} :=
    ⟨baseOrdered n, rfl⟩
  let deck := hp.fundamentalGroupToMulOpposite e
  let geom :=
    FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)
  let swaps :=
    FreeGroup.lift (fun i : Fin (n - 1) =>
      Equiv.swap (strandIdx i) (strandIdxSucc i))
  let invOp := MulEquiv.inv' (Equiv.Perm (Fin n))
  have hcomp : deck.comp geom = invOp.toMonoidHom.comp swaps := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply]
    rw [show geom (FreeGroup.of i) = halfTwistBraid n i by simp [geom]]
    rw [show swaps (FreeGroup.of i) =
      Equiv.swap (strandIdx i) (strandIdxSucc i) by simp [swaps]]
    calc
      deck (halfTwistBraid n i) =
          MulOpposite.op (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by
        simpa [deck, e] using hgen i
      _ = invOp.toMonoidHom
          (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by
        change
          MulOpposite.op (Equiv.swap (strandIdx i) (strandIdxSucc i)) =
            MulOpposite.op ((Equiv.swap (strandIdx i) (strandIdxSucc i))⁻¹)
        rw [Equiv.swap_inv]
  obtain ⟨w, hw⟩ := hswap (invOp.symm (deck β))
  have hw' : swaps w = invOp.symm (deck β) := by
    simpa [swaps] using hw
  have hdeck : deck (geom w) = deck β := by
    calc
      deck (geom w) = invOp.toMonoidHom (swaps w) := by
        have h := DFunLike.congr_fun hcomp w
        simpa only [MonoidHom.comp_apply] using h
      _ = invOp.toMonoidHom (invOp.symm (deck β)) := by rw [hw']
      _ = deck β := by
        change invOp (invOp.symm (deck β)) = deck β
        exact invOp.apply_symm_apply _
  refine ⟨w, ?_⟩
  change β * (geom w)⁻¹ ∈ deck.ker
  rw [MonoidHom.mem_ker, map_mul, map_inv, hdeck, mul_inv_cancel]
