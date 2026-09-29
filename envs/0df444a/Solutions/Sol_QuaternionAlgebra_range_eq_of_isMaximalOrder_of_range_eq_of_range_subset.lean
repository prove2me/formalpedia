-- Prove2me | solution 1 for QuaternionAlgebra.range_eq_of_isMaximalOrder_of_range_eq_of_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/15a50e1b-f185-56e7-94df-4b3e0aa9fcbc

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion

noncomputable section

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "lift lift_apply Basis.mk mk Basis exists_natCast_smul_mem_of_mem_span IsMaximalOrder IsOrder"
namespace MaximalOrderTransport
p2m_open "QuaternionAlgebra"

variable {a b : ℚ}

theorem nsmul_right_injective_quat {n : ℕ} (hn : n ≠ 0) :
    Function.Injective fun z : ℍ[ℚ, a, b] => n • z := by
  intro z w h
  have h' : (n : ℚ) • z = (n : ℚ) • w := by
    simpa only [Nat.cast_smul_eq_nsmul] using h
  exact smul_right_injective ℍ[ℚ, a, b] (Nat.cast_ne_zero.mpr hn) h'

theorem isAddTorsionFree_quat : IsAddTorsionFree ℍ[ℚ, a, b] :=
  ⟨fun _ hn => nsmul_right_injective_quat hn⟩

theorem isAddTorsionFree_submodule (Λ : Submodule ℤ ℍ[ℚ, a, b]) : IsAddTorsionFree ↥Λ := by
  refine ⟨fun n hn y y' h => Subtype.ext (nsmul_right_injective_quat hn ?_)⟩
  have h' : n • y = n • y' := h
  have := congrArg Subtype.val h'
  simpa only [Submodule.coe_smul_of_tower] using this

theorem free_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : Module.Free ℤ ↥Λ := by
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg
  haveI : IsAddTorsionFree ↥Λ := isAddTorsionFree_submodule Λ
  exact Module.free_of_finite_type_torsion_free'

theorem finite_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : Module.Finite ℤ ↥Λ :=
  Module.Finite.iff_fg.mpr hΛ.fg

variable {E : Type*} [Ring E]

structure Frame (θ θ' : E →+* ℍ[ℚ, a, b]) (Λ' : Submodule ℤ ℍ[ℚ, a, b]) : Prop where
  inj : Function.Injective θ
  inj' : Function.Injective θ'
  isOrder : IsOrder Λ'
  range_eq : Set.range θ = (Λ' : Set ℍ[ℚ, a, b])

variable {θ θ' : E →+* ℍ[ℚ, a, b]} {Λ' : Submodule ℤ ℍ[ℚ, a, b]}

theorem Frame.mem_range (hF : Frame θ θ' Λ') {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ') : y ∈ Set.range θ := by
  rw [hF.range_eq]; exact hy

theorem Frame.apply_mem (hF : Frame θ θ' Λ') (e : E) : θ e ∈ Λ' := by
  have : θ e ∈ Set.range θ := ⟨e, rfl⟩
  rw [hF.range_eq] at this
  exact this

def lift (hF : Frame θ θ' Λ') (y : ℍ[ℚ, a, b]) (hy : y ∈ Λ') : E :=
  (hF.mem_range hy).choose

theorem apply_lift (hF : Frame θ θ' Λ') (y : ℍ[ℚ, a, b]) (hy : y ∈ Λ') : θ (lift hF y hy) = y :=
  (hF.mem_range hy).choose_spec

theorem lift_apply (hF : Frame θ θ' Λ') (e : E) : lift hF (θ e) (hF.apply_mem e) = e :=
  hF.inj (apply_lift hF _ _)

theorem lift_add (hF : Frame θ θ' Λ') {y z : ℍ[ℚ, a, b]} (hy : y ∈ Λ') (hz : z ∈ Λ') :
    lift hF (y + z) (Λ'.add_mem hy hz) = lift hF y hy + lift hF z hz :=
  hF.inj (by rw [map_add, apply_lift, apply_lift, apply_lift])

theorem lift_mul (hF : Frame θ θ' Λ') {y z : ℍ[ℚ, a, b]} (hy : y ∈ Λ') (hz : z ∈ Λ') :
    lift hF (y * z) (hF.isOrder.mul_mem hy hz) = lift hF y hy * lift hF z hz :=
  hF.inj (by rw [map_mul, apply_lift, apply_lift, apply_lift])

theorem lift_one (hF : Frame θ θ' Λ') : lift hF 1 hF.isOrder.one_mem = 1 :=
  hF.inj (by rw [map_one, apply_lift])

theorem lift_zero (hF : Frame θ θ' Λ') : lift hF 0 Λ'.zero_mem = 0 :=
  hF.inj (by rw [map_zero, apply_lift])

theorem lift_congr (hF : Frame θ θ' Λ') {y z : ℍ[ℚ, a, b]} (hy : y ∈ Λ') (hz : z ∈ Λ') (h : y = z) :
    lift hF y hy = lift hF z hz := by
  subst h; rfl

def PhiL (hF : Frame θ θ' Λ') : ↥Λ' →ₗ[ℤ] ℍ[ℚ, a, b] :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun y => θ' (lift hF (y : ℍ[ℚ, a, b]) y.2)
      map_zero' := by
        change θ' (lift hF (0 : ℍ[ℚ, a, b]) Λ'.zero_mem) = 0
        rw [lift_zero, map_zero]
      map_add' := fun y z => by
        change θ' (lift hF ((y : ℍ[ℚ, a, b]) + z) (Λ'.add_mem y.2 z.2)) = _
        rw [lift_add, map_add] }

@[scoped simp] theorem PhiL_apply (hF : Frame θ θ' Λ') (y : ↥Λ') :
    PhiL hF y = θ' (lift hF (y : ℍ[ℚ, a, b]) y.2) := rfl

def bZ (hF : Frame θ θ' Λ') : Module.Basis (Fin (Module.finrank ℤ ↥Λ')) ℤ ↥Λ' := by
  haveI := free_of_isOrder hF.isOrder
  haveI := finite_of_isOrder hF.isOrder
  exact Module.finBasis ℤ ↥Λ'

def v (hF : Frame θ θ' Λ') (i : Fin (Module.finrank ℤ ↥Λ')) : ℍ[ℚ, a, b] := (bZ hF i : ℍ[ℚ, a, b])

theorem v_mem (hF : Frame θ θ' Λ') (i : Fin (Module.finrank ℤ ↥Λ')) : v hF i ∈ Λ' := (bZ hF i).2

theorem linearIndependent_v_int (hF : Frame θ θ' Λ') : LinearIndependent ℤ (v hF) :=
  (bZ hF).linearIndependent.map' Λ'.subtype (Submodule.ker_subtype Λ')

theorem linearIndependent_v (hF : Frame θ θ' Λ') : LinearIndependent ℚ (v hF) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).mp (linearIndependent_v_int hF)

theorem mem_span_v_int (hF : Frame θ θ' Λ') {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ') :
    y ∈ Submodule.span ℤ (Set.range (v hF)) := by
  have h1 : (⟨y, hy⟩ : ↥Λ') ∈ Submodule.span ℤ (Set.range (bZ hF)) := by
    rw [(bZ hF).span_eq]; trivial
  have h2 := Submodule.mem_map_of_mem (f := Λ'.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

theorem top_le_span_v (hF : Frame θ θ' Λ') : ⊤ ≤ Submodule.span ℚ (Set.range (v hF)) := by
  rw [← hF.isOrder.spanTop]
  refine Submodule.span_le.mpr fun y hy => ?_
  exact Submodule.span_le_restrictScalars ℤ ℚ _ (mem_span_v_int hF hy)

def B (hF : Frame θ θ' Λ') : Module.Basis (Fin (Module.finrank ℤ ↥Λ')) ℚ ℍ[ℚ, a, b] :=
  Module.Basis.mk (linearIndependent_v hF) (top_le_span_v hF)

@[scoped simp] theorem B_apply (hF : Frame θ θ' Λ') (i : Fin (Module.finrank ℤ ↥Λ')) : B hF i = v hF i :=
  Module.Basis.mk_apply _ _ i

def phi (hF : Frame θ θ' Λ') : ℍ[ℚ, a, b] →ₗ[ℚ] ℍ[ℚ, a, b] :=
  (B hF).constr ℚ fun i => θ' (lift hF (v hF i) (v_mem hF i))

theorem phi_v (hF : Frame θ θ' Λ') (i : Fin (Module.finrank ℤ ↥Λ')) :
    phi hF (v hF i) = θ' (lift hF (v hF i) (v_mem hF i)) := by
  have : phi hF (B hF i) = θ' (lift hF (v hF i) (v_mem hF i)) := Module.Basis.constr_basis _ _ _ _
  rwa [B_apply] at this

theorem phi_of_mem (hF : Frame θ θ' Λ') (y : ℍ[ℚ, a, b]) (hy : y ∈ Λ') :
    phi hF y = θ' (lift hF y hy) := by
  have key : (phi hF).restrictScalars ℤ ∘ₗ Λ'.subtype = PhiL hF := by
    refine (bZ hF).ext fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply, PhiL_apply]
    exact phi_v hF i
  have := LinearMap.congr_fun key ⟨y, hy⟩
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply, PhiL_apply] at this
  exact this

theorem phi_one (hF : Frame θ θ' Λ') : phi hF 1 = 1 := by
  rw [phi_of_mem hF 1 hF.isOrder.one_mem, lift_one, map_one]

theorem phi_mul (hF : Frame θ θ' Λ') (y z : ℍ[ℚ, a, b]) : phi hF (y * z) = phi hF y * phi hF z := by
  have key : (LinearMap.mul ℚ ℍ[ℚ, a, b]).compr₂ (phi hF) =
      (LinearMap.mul ℚ ℍ[ℚ, a, b]).compl₁₂ (phi hF) (phi hF) := by
    refine LinearMap.ext_basis (B hF) (B hF) fun i j => ?_
    rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.mul_apply', B_apply,
      B_apply, phi_of_mem hF _ (hF.isOrder.mul_mem (v_mem hF i) (v_mem hF j)), phi_v, phi_v, ← map_mul,
      lift_mul]
  have := LinearMap.congr_fun (LinearMap.congr_fun key y) z
  rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.mul_apply'] at this
  exact this

theorem phi_injective (hF : Frame θ θ' Λ') : Function.Injective (phi hF) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hzspan : z ∈ Submodule.span ℚ (Λ' : Set ℍ[ℚ, a, b]) := by rw [hF.isOrder.spanTop]; trivial
  obtain ⟨n, hn, hnz⟩ := exists_natCast_smul_mem_of_mem_span hzspan
  have h1 : phi hF (((n : ℕ) : ℤ) • z) = 0 := by rw [map_zsmul, hz, smul_zero]
  rw [phi_of_mem hF _ hnz] at h1
  have h2 : lift hF _ hnz = 0 := hF.inj' (by rw [h1, map_zero])
  have h3 : ((n : ℕ) : ℤ) • z = 0 := by rw [← apply_lift hF _ hnz, h2, map_zero]
  rw [natCast_zsmul] at h3
  exact nsmul_right_injective_quat hn (h3.trans (smul_zero n).symm)

def phiA (hF : Frame θ θ' Λ') : ℍ[ℚ, a, b] →ₐ[ℚ] ℍ[ℚ, a, b] :=
  AlgHom.ofLinearMap (phi hF) (phi_one hF) (phi_mul hF)

theorem phiA_bijective (hF : Frame θ θ' Λ') : Function.Bijective (phiA hF) :=
  ⟨phi_injective hF, LinearMap.injective_iff_surjective.mp (phi_injective hF)⟩

def phiE (hF : Frame θ θ' Λ') : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a, b] :=
  AlgEquiv.ofBijective (phiA hF) (phiA_bijective hF)

theorem phiE_apply (hF : Frame θ θ' Λ') (z : ℍ[ℚ, a, b]) : phiE hF z = phi hF z := rfl

theorem range_eq_image (hF : Frame θ θ' Λ') :
    Set.range θ' = (phiE hF) '' (Λ' : Set ℍ[ℚ, a, b]) := by
  ext w
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨θ e, hF.apply_mem e, ?_⟩
    rw [phiE_apply, phi_of_mem hF _ (hF.apply_mem e), lift_apply]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨lift hF y hy, by rw [phiE_apply, phi_of_mem hF y hy]⟩

def intMap (ψ : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] :=
  (ψ : ℍ[ℚ, a, b] →ₐ[ℚ] ℍ[ℚ, a, b]).toLinearMap.restrictScalars ℤ

@[scoped simp] theorem intMap_apply (ψ : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) : intMap ψ z = ψ z := rfl

theorem coe_map_intMap (ψ : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a, b]) (O : Submodule ℤ ℍ[ℚ, a, b]) :
    ((O.map (intMap ψ) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = ψ '' (O : Set ℍ[ℚ, a, b]) := by
  rw [Submodule.map_coe]; rfl

theorem isOrder_map (ψ : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a, b]) {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) :
    IsOrder (O.map (intMap ψ)) where
  one_mem := ⟨1, hO.one_mem, map_one ψ⟩
  mul_mem := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y * z, hO.mul_mem hy hz, map_mul ψ y z⟩
  spanTop := by
    rw [coe_map_intMap]
    have : ⇑ψ '' (O : Set ℍ[ℚ, a, b]) =
        ⇑((ψ : ℍ[ℚ, a, b] →ₐ[ℚ] ℍ[ℚ, a, b]).toLinearMap) '' (O : Set ℍ[ℚ, a, b]) := rfl
    rw [this, Submodule.span_image, hO.spanTop, Submodule.map_top, LinearMap.range_eq_top]
    exact ψ.surjective
  fg := hO.fg.map _

theorem mem_map_intMap_iff (ψ : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a, b]) (O : Submodule ℤ ℍ[ℚ, a, b]) (w : ℍ[ℚ, a, b]) :
    w ∈ O.map (intMap ψ) ↔ ψ.symm w ∈ O := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [intMap_apply, AlgEquiv.symm_apply_apply]
    exact hy
  · intro h
    exact ⟨ψ.symm w, h, by rw [intMap_apply, AlgEquiv.apply_symm_apply]⟩

theorem isMaximalOrder_map (ψ : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a, b]) {O : Submodule ℤ ℍ[ℚ, a, b]}
    (hO : IsMaximalOrder O) : IsMaximalOrder (O.map (intMap ψ)) := by
  refine ⟨isOrder_map ψ hO.1, fun O' hO' hle => ?_⟩
  have h1 : IsOrder (O'.map (intMap ψ.symm)) := isOrder_map ψ.symm hO'
  have h2 : O ≤ O'.map (intMap ψ.symm) := by
    intro y hy
    rw [mem_map_intMap_iff, AlgEquiv.symm_symm]
    exact hle ⟨y, hy, rfl⟩
  have h3 := hO.2 _ h1 h2
  refine le_antisymm (fun w hw => ?_) hle
  rw [mem_map_intMap_iff, ← h3, mem_map_intMap_iff, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  exact hw

theorem Frame.range_eq_of_subset (hF : Frame θ θ' Λ') (hΛ' : IsMaximalOrder Λ') {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : IsMaximalOrder Λ) (hsub : Set.range θ' ⊆ (Λ : Set ℍ[ℚ, a, b])) :
    Set.range θ' = (Λ : Set ℍ[ℚ, a, b]) := by
  have hO : IsMaximalOrder (Λ'.map (intMap (phiE hF))) := isMaximalOrder_map (phiE hF) hΛ'
  have hcoe : ((Λ'.map (intMap (phiE hF)) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = Set.range θ' := by
    rw [coe_map_intMap, range_eq_image hF]
  have hle : Λ'.map (intMap (phiE hF)) ≤ Λ := by
    intro w hw
    have : w ∈ Set.range θ' := by rw [← hcoe]; exact hw
    exact hsub this
  have := hO.2 Λ hΛ.1 hle
  rw [← hcoe, this]

end QuaternionAlgebra.MaximalOrderTransport
p2m_reactivate "P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset.QuaternionAlgebra P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset.QuaternionAlgebra.MaximalOrderTransport"
p2m_reactivate "P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset.QuaternionAlgebra"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset.QuaternionAlgebra P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset.QuaternionAlgebra.MaximalOrderTransport"

open QuaternionAlgebra.MaximalOrderTransport in
theorem solution
    {a b : ℚ} {E : Type*} [Ring E] (θ θ' : E →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθ' : Function.Injective θ')
    {Λ' Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ' : QuaternionAlgebra.IsMaximalOrder Λ') (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (hrange : Set.range θ = (Λ' : Set ℍ[ℚ, a, b])) (hsub : Set.range θ' ⊆ (Λ : Set ℍ[ℚ, a, b])) :
    Set.range θ' = (Λ : Set ℍ[ℚ, a, b]) :=
  Frame.range_eq_of_subset ⟨hθ, hθ', hΛ'.1, hrange⟩ hΛ' hΛ hsub

end S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset
end P2MW
export P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset (solution)
