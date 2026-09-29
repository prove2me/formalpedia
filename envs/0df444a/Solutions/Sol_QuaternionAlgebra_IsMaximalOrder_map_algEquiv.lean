-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.map_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2d3742c6-510a-5ae6-9d81-b52ce03330ff

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_map_algEquiv

set_option autoImplicit false

open scoped Quaternion

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "IsMaximalOrder IsOrder"
p2m_open "QuaternionAlgebra"

namespace IsOrder p2m_export "QuaternionAlgebra.IsOrder" "mul_mem spanTop one_mem fg" end IsOrder
namespace IsOrder
p2m_open_scoped "QuaternionAlgebra.IsOrder" in

private theorem _root_.QuaternionAlgebra.IsOrder.map_algEquiv {a b a' b' : ℚ}
    (e : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (h : IsOrder Λ) : IsOrder (Λ.map (e.toLinearMap.restrictScalars ℤ)) where
  one_mem := ⟨1, h.one_mem, by simp⟩
  mul_mem := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, h.mul_mem hx hy, by simp⟩
  spanTop := by
    have hset : ((Λ.map (e.toLinearMap.restrictScalars ℤ) : Submodule ℤ ℍ[ℚ, a', b']) :
        Set ℍ[ℚ, a', b']) = e.toLinearMap '' (Λ : Set ℍ[ℚ, a, b]) := by
      ext y
      simp
    rw [hset, Submodule.span_image, h.spanTop, Submodule.map_top, LinearMap.range_eq_top]
    exact e.surjective
  fg := h.fg.map _

end IsOrder
p2m_export "QuaternionAlgebra" "IsOrder.map_algEquiv"
end QuaternionAlgebra

namespace QuaternionAlgebra p2m_export "QuaternionAlgebra" "IsMaximalOrder IsOrder" namespace IsMaximalOrder end QuaternionAlgebra.IsMaximalOrder
namespace QuaternionAlgebra.IsMaximalOrder
p2m_open_scoped "QuaternionAlgebra QuaternionAlgebra.IsMaximalOrder" in

private theorem _root_.QuaternionAlgebra.IsMaximalOrder.map_algEquiv {a b a' b' : ℚ}
    (e : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    QuaternionAlgebra.IsMaximalOrder (Λ.map (e.toLinearMap.restrictScalars ℤ)) := by
  refine ⟨hΛ.1.map_algEquiv e, fun Λ' hΛ' hle => ?_⟩
  have key : Λ'.map (e.symm.toLinearMap.restrictScalars ℤ) = Λ := by
    apply hΛ.2 _ (hΛ'.map_algEquiv e.symm)
    intro x hx
    exact ⟨e x, hle ⟨x, hx, rfl⟩, by simp⟩
  have back : Λ' = (Λ'.map (e.symm.toLinearMap.restrictScalars ℤ)).map
      (e.toLinearMap.restrictScalars ℤ) := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
  rw [back, key]

end QuaternionAlgebra.IsMaximalOrder
p2m_export "" "QuaternionAlgebra.IsMaximalOrder.map_algEquiv"

theorem solution {a b a' b' : ℚ}
    (e : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    QuaternionAlgebra.IsMaximalOrder (Λ.map (e.toLinearMap.restrictScalars ℤ)) :=
  QuaternionAlgebra.IsMaximalOrder.map_algEquiv e hΛ

end S_QuaternionAlgebra_IsMaximalOrder_map_algEquiv
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_map_algEquiv (solution)
