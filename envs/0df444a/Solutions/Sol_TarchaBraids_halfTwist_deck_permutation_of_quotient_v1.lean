-- Prove2me | solution 1 for TarchaBraids.halfTwist_deck_permutation_of_quotient_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T04:16:59.16624+00:00
-- url     : https://prove2.me/submissions/4e693866-8e42-4d68-aed8-a5c6be8c3472

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1

open BraidsLinksMCG TarchaBraids unitInterval

theorem solution (n : ℕ) (i : Fin (n - 1))
    (hp : IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n))) :
    hp.fundamentalGroupToMulOpposite
      (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})
      (halfTwistBraid n i) =
    MulOpposite.op (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by
  have he : configProj n (baseOrdered n) = baseUnordered n := rfl
  let e : (configProj n) ⁻¹' {baseUnordered n} :=
    ⟨baseOrdered n, by simpa using he⟩
  have hend : configProj n (halfTwistConfig n i 1) = baseUnordered n := by
    exact (halfTwistLoop n i).target
  let ey : (configProj n) ⁻¹' {baseUnordered n} :=
    ⟨halfTwistConfig n i 1, by simpa using hend⟩
  have hmon :
      hp.isCoveringMap.monodromy (halfTwistBraid n i) e = ey := by
    let Γ : Path (baseOrdered n) (halfTwistConfig n i 1) :=
      { toFun := fun t => halfTwistConfig n i (t : ℝ)
        continuous_toFun :=
          (continuous_halfTwistConfig n i).comp continuous_subtype_val
        source' := by
          simp only [Set.Icc.coe_zero, halfTwistConfig_zero]
        target' := by
          simp only [Set.Icc.coe_one] }
    have hmap :
        (Path.Homotopic.Quotient.mk Γ).map
            ⟨configProj n, (configProj n).continuous⟩ =
          Path.Homotopic.Quotient.cast (halfTwistBraid n i) he hend := by
      change
        (Path.Homotopic.Quotient.mk Γ).map
            ⟨configProj n, (configProj n).continuous⟩ =
          (Path.Homotopic.Quotient.mk (halfTwistLoop n i)).cast he hend
      rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      rfl
    refine hp.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk Γ) ?_
    simpa only [e, ey, Set.mem_preimage, Set.mem_singleton_iff] using hmap
  rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
  rw [hmon]
  change
    orderedConfigPermute
        (Equiv.swap (strandIdx i) (strandIdxSucc i)) (baseOrdered n) =
      halfTwistConfig n i 1
  apply Subtype.ext
  funext k
  have h := congrFun (halfTwistConfig_one n i)
    ((Equiv.swap (strandIdx i) (strandIdxSucc i)) k)
  simpa [orderedConfigPermute, Function.comp_apply] using h
