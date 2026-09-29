-- Prove2me | solution 1 for PDivisibleGroup.exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fda269aa-52d4-542d-8809-17db0f6a76cc

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule"
p2m_attr_erase "simp" "PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent PDivisibleGroup.baseChange_level PDivisibleGroup.cotangentMap_toCotangent HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul closureCounit_apply genericFibreAlgHom_tmul"
p2m_attr_erase "simp" "tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply"
p2m_attr_erase "simp" "CartierDual.mapLinear_apply PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map"

set_option autoImplicit false

namespace RaynaudUniq

theorem apply_eq_of_apply_eq {M N N' : Type*} [CommGroup M] [Group N] [Group N'] (Φ : M →* N) (Φ' : M →* N')
    (hker : ∀ y, Φ y = 1 ↔ Φ' y = 1) {x x' : M} (hx : Φ x = Φ x') : Φ' x = Φ' x' := by
  rw [← div_eq_one, ← map_div] at hx ⊢
  exact (hker _).1 hx

end RaynaudUniq

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "transition level Hopf.convCompMonoidHom Point Point.toAlgHom Point.ofAlgHom Point.ext pointIncl pointInclLE pointInclLE_self pointInclLE_succ pointsDirectedSystemMap Points pointsMkAdd Points.induction_on pointMap Points.smul_pointsMkAdd existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime"
p2m_open "PDivisibleGroup"

variable {R : Type} [CommRing R] {p h h' : ℕ} (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h')
  (L : Type) [CommRing L] [Algebra R L]

theorem pointInclLE_family {f : ∀ w, G.Point L w →* H.Point L w}
    (hf : ∀ (w : ℕ) (x : G.Point L w), f (w + 1) (G.pointIncl L w x) = H.pointIncl L w (f w x))
    {v w : ℕ} (hvw : v ≤ w) (x : G.Point L v) :
    f w (G.pointInclLE L hvw x) = H.pointInclLE L hvw (f v x) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self, H.pointInclLE_self]
  | step hvw ih => rw [G.pointInclLE_succ hvw, H.pointInclLE_succ hvw, hf, ih]

noncomputable def pointsLift (f : ∀ w, G.Point L w →* H.Point L w)
    (hf : ∀ (w : ℕ) (x : G.Point L w), f (w + 1) (G.pointIncl L w x) = H.pointIncl L w (f w x)) :
    G.Points L →+ H.Points L :=
  AddCommGroup.DirectLimit.map (G := fun v => Additive (G.Point L v)) (G' := fun v => Additive (H.Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => H.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (f v))
    (fun _ _ hvw => AddMonoidHom.ext fun x =>
      congrArg Additive.ofMul (pointInclLE_family G H L hf hvw (Additive.toMul x)))

@[scoped simp] theorem pointsLift_mkAdd (f : ∀ w, G.Point L w →* H.Point L w)
    (hf : ∀ (w : ℕ) (x : G.Point L w), f (w + 1) (G.pointIncl L w x) = H.pointIncl L w (f w x))
    (v : ℕ) (x : G.Point L v) :
    pointsLift G H L f hf (G.pointsMkAdd L v (Additive.ofMul x)) = H.pointsMkAdd L v (Additive.ofMul (f v x)) :=
  AddCommGroup.DirectLimit.map_apply_of (G := fun v => Additive (G.Point L v)) (G' := fun v => Additive (H.Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => H.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (f v)) _ (Additive.ofMul x)

theorem pointsLift_smul (f : ∀ w, G.Point L w →* H.Point L w)
    (hf : ∀ (w : ℕ) (x : G.Point L w), f (w + 1) (G.pointIncl L w x) = H.pointIncl L w (f w x))
    (hgal : ∀ (σ : L ≃ₐ[R] L) (w : ℕ) (x : G.Point L w), f w (G.pointMap (σ : L →ₐ[R] L) w x) = H.pointMap (σ : L →ₐ[R] L) w (f w x))
    (σ : L ≃ₐ[R] L) (z : G.Points L) :
    pointsLift G H L f hf (σ • z) = σ • pointsLift G H L f hf z := by
  induction z using Points.induction_on with
  | ih w x => rw [Points.smul_pointsMkAdd, pointsLift_mkAdd, pointsLift_mkAdd, Points.smul_pointsMkAdd, hgal]

end PDivisibleGroup
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime.PDivisibleGroup"

theorem solution
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h hB hB₀ : ℕ} (𝒢 : PDivisibleGroup Rh p h) (ℬ : PDivisibleGroup Rh p hB) (ℬ₀ : PDivisibleGroup Rh p hB₀)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v) (ψ₀ : ∀ v : ℕ, ℬ₀.level v →ₐc[Rh] 𝒢.level v)
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψ₀t : ∀ v : ℕ, (𝒢.transition v).comp (ψ₀ (v + 1)) = (ψ₀ v).comp (ℬ₀.transition v))

    (hker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ₀ v : ℬ₀.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ₀.Point (AlgebraicClosure ℚ) v))

    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    (hψ₀surj : ∀ (v : ℕ) (b : ℬ₀.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ₀ v : ℬ₀.level v →ₐ[Rh] 𝒢.level v)) = b)

    (hr₀ : ∀ v : ℕ, ∃ r : 𝒢.level v →ₗ[Rh] ℬ₀.level v, ∀ b : ℬ₀.level v, r (ψ₀ v b) = b) :
    ∀ v : ℕ, ∃ r : 𝒢.level v →ₗ[Rh] ℬ.level v, ∀ b : ℬ.level v, r (ψ v b) = b := by
  classical
  intro v

  let Φ : ∀ w : ℕ, 𝒢.Point (AlgebraicClosure ℚ) w →* ℬ.Point (AlgebraicClosure ℚ) w := fun w =>
    PDivisibleGroup.Hopf.convCompMonoidHom (AlgebraicClosure ℚ) (ψ w)
  let Φ₀ : ∀ w : ℕ, 𝒢.Point (AlgebraicClosure ℚ) w →* ℬ₀.Point (AlgebraicClosure ℚ) w := fun w =>
    PDivisibleGroup.Hopf.convCompMonoidHom (AlgebraicClosure ℚ) (ψ₀ w)
  have hΦ : ∀ (w : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) w), Φ w x =
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ w : ℬ.level w →ₐ[Rh] 𝒢.level w)) :=
    fun _ _ => rfl
  have hΦ₀ : ∀ (w : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) w), Φ₀ w x =
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ₀ w : ℬ₀.level w →ₐ[Rh] 𝒢.level w)) :=
    fun _ _ => rfl
  have hsurj : ∀ w, Function.Surjective (Φ w) := hψsurj
  have hsurj₀ : ∀ w, Function.Surjective (Φ₀ w) := hψ₀surj
  have hk : ∀ (w : ℕ) (y : 𝒢.Point (AlgebraicClosure ℚ) w), Φ w y = 1 ↔ Φ₀ w y = 1 := hker

  have hΦincl : ∀ (w : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) w),
      Φ (w + 1) (𝒢.pointIncl (AlgebraicClosure ℚ) w x) = ℬ.pointIncl (AlgebraicClosure ℚ) w (Φ w x) := by
    intro w x
    refine PDivisibleGroup.Point.ext fun a => ?_
    change PDivisibleGroup.Point.toAlgHom x (𝒢.transition w (ψ (w + 1) a)) =
      PDivisibleGroup.Point.toAlgHom x (ψ w (ℬ.transition w a))
    rw [show 𝒢.transition w (ψ (w + 1) a) = ψ w (ℬ.transition w a) from DFunLike.congr_fun (hψt w) a]
  have hΦ₀incl : ∀ (w : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) w),
      Φ₀ (w + 1) (𝒢.pointIncl (AlgebraicClosure ℚ) w x) = ℬ₀.pointIncl (AlgebraicClosure ℚ) w (Φ₀ w x) := by
    intro w x
    refine PDivisibleGroup.Point.ext fun a => ?_
    change PDivisibleGroup.Point.toAlgHom x (𝒢.transition w (ψ₀ (w + 1) a)) =
      PDivisibleGroup.Point.toAlgHom x (ψ₀ w (ℬ₀.transition w a))
    rw [show 𝒢.transition w (ψ₀ (w + 1) a) = ψ₀ w (ℬ₀.transition w a) from DFunLike.congr_fun (hψ₀t w) a]
  have hΦgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (w : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) w),
      Φ w (𝒢.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w x) =
        ℬ.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w (Φ w x) :=
    fun _ _ _ => PDivisibleGroup.Point.ext fun _ => rfl
  have hΦ₀gal' : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (w : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) w),
      Φ₀ w (𝒢.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w x) =
        ℬ₀.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w (Φ₀ w x) :=
    fun _ _ _ => PDivisibleGroup.Point.ext fun _ => rfl

  have P1 : ∀ w : ℕ, ∃ e : ℬ.Point (AlgebraicClosure ℚ) w ≃* ℬ₀.Point (AlgebraicClosure ℚ) w,
      ∀ x : 𝒢.Point (AlgebraicClosure ℚ) w, e (Φ w x) = Φ₀ w x := by
    intro w
    have h1 : ∀ {x x' : 𝒢.Point (AlgebraicClosure ℚ) w}, Φ w x = Φ w x' → Φ₀ w x = Φ₀ w x' :=
      fun hx => RaynaudUniq.apply_eq_of_apply_eq (Φ w) (Φ₀ w) (hk w) hx
    have h2 : ∀ {x x' : 𝒢.Point (AlgebraicClosure ℚ) w}, Φ₀ w x = Φ₀ w x' → Φ w x = Φ w x' :=
      fun hx => RaynaudUniq.apply_eq_of_apply_eq (Φ₀ w) (Φ w) (fun y => (hk w y).symm) hx
    choose lift hlift using hsurj w
    let e₀ : ℬ.Point (AlgebraicClosure ℚ) w →* ℬ₀.Point (AlgebraicClosure ℚ) w :=
      { toFun := fun b => Φ₀ w (lift b)
        map_one' := by
          rw [← map_one (Φ₀ w)]
          exact h1 ((hlift 1).trans (map_one (Φ w)).symm)
        map_mul' := fun b b' => by
          rw [← map_mul]
          apply h1
          rw [map_mul, hlift, hlift, hlift] }
    have he₀ : ∀ x, e₀ (Φ w x) = Φ₀ w x := fun x => h1 (hlift _)
    refine ⟨MulEquiv.ofBijective e₀ ⟨?_, ?_⟩, he₀⟩
    · intro b b' hbb'
      rw [← hlift b, ← hlift b']
      exact h2 hbb'
    · intro b₀
      obtain ⟨x, hx⟩ := hsurj₀ w b₀
      exact ⟨Φ w x, (he₀ x).trans hx⟩
  choose e he using P1

  have hecompat : ∀ (w : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) w),
      (e (w + 1) : ℬ.Point (AlgebraicClosure ℚ) (w + 1) →* ℬ₀.Point (AlgebraicClosure ℚ) (w + 1))
          (ℬ.pointIncl (AlgebraicClosure ℚ) w b) =
        ℬ₀.pointIncl (AlgebraicClosure ℚ) w
          ((e w : ℬ.Point (AlgebraicClosure ℚ) w →* ℬ₀.Point (AlgebraicClosure ℚ) w) b) := by
    intro w b
    obtain ⟨x, rfl⟩ := hsurj w b
    rw [MonoidHom.coe_coe, MonoidHom.coe_coe, ← hΦincl, he, he, hΦ₀incl]
  have hecompat' : ∀ (w : ℕ) (b₀ : ℬ₀.Point (AlgebraicClosure ℚ) w),
      ((e (w + 1)).symm : ℬ₀.Point (AlgebraicClosure ℚ) (w + 1) →* ℬ.Point (AlgebraicClosure ℚ) (w + 1))
          (ℬ₀.pointIncl (AlgebraicClosure ℚ) w b₀) =
        ℬ.pointIncl (AlgebraicClosure ℚ) w
          (((e w).symm : ℬ₀.Point (AlgebraicClosure ℚ) w →* ℬ.Point (AlgebraicClosure ℚ) w) b₀) := by
    intro w b₀
    rw [MonoidHom.coe_coe, MonoidHom.coe_coe]
    apply (e (w + 1)).injective
    have := hecompat w ((e w).symm b₀)
    rw [MonoidHom.coe_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply] at this
    rw [MulEquiv.apply_symm_apply, this]
  have hegal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (w : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) w),
      (e w : ℬ.Point (AlgebraicClosure ℚ) w →* ℬ₀.Point (AlgebraicClosure ℚ) w)
          (ℬ.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w b) =
        ℬ₀.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w
          ((e w : ℬ.Point (AlgebraicClosure ℚ) w →* ℬ₀.Point (AlgebraicClosure ℚ) w) b) := by
    intro τ w b
    obtain ⟨x, rfl⟩ := hsurj w b
    rw [MonoidHom.coe_coe, ← hΦgal, he, he, hΦ₀gal']
  have hegal' : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (w : ℕ) (b₀ : ℬ₀.Point (AlgebraicClosure ℚ) w),
      ((e w).symm : ℬ₀.Point (AlgebraicClosure ℚ) w →* ℬ.Point (AlgebraicClosure ℚ) w)
          (ℬ₀.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w b₀) =
        ℬ.pointMap (τ : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w
          (((e w).symm : ℬ₀.Point (AlgebraicClosure ℚ) w →* ℬ.Point (AlgebraicClosure ℚ) w) b₀) := by
    intro τ w b₀
    rw [MonoidHom.coe_coe]
    apply (e w).injective
    have := hegal τ w ((e w).symm b₀)
    rw [MonoidHom.coe_coe, MulEquiv.apply_symm_apply] at this
    rw [MulEquiv.apply_symm_apply, this]
  let Efwd : ℬ.Points (AlgebraicClosure ℚ) →+ ℬ₀.Points (AlgebraicClosure ℚ) :=
    PDivisibleGroup.pointsLift ℬ ℬ₀ (AlgebraicClosure ℚ) (fun w => (e w : _ →* _)) hecompat
  let Ebwd : ℬ₀.Points (AlgebraicClosure ℚ) →+ ℬ.Points (AlgebraicClosure ℚ) :=
    PDivisibleGroup.pointsLift ℬ₀ ℬ (AlgebraicClosure ℚ) (fun w => ((e w).symm : _ →* _)) hecompat'
  have hEfwd : ∀ (w : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) w),
      Efwd (ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b)) =
        ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (e w b)) := fun w b => by
    rw [PDivisibleGroup.pointsLift_mkAdd, MonoidHom.coe_coe]
  have hEbwd : ∀ (w : ℕ) (b₀ : ℬ₀.Point (AlgebraicClosure ℚ) w),
      Ebwd (ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b₀)) =
        ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul ((e w).symm b₀)) := fun w b₀ => by
    rw [PDivisibleGroup.pointsLift_mkAdd, MonoidHom.coe_coe]
  have hEE₁ : Ebwd.comp Efwd = AddMonoidHom.id _ := by
    ext z
    induction z using PDivisibleGroup.Points.induction_on with
    | ih w b => rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, hEfwd, hEbwd, MulEquiv.symm_apply_apply]
  have hEE₂ : Efwd.comp Ebwd = AddMonoidHom.id _ := by
    ext z
    induction z using PDivisibleGroup.Points.induction_on with
    | ih w b₀ => rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, hEbwd, hEfwd, MulEquiv.apply_symm_apply]
  have P2 : ∃ E : ℬ.Points (AlgebraicClosure ℚ) ≃+ ℬ₀.Points (AlgebraicClosure ℚ),
      (∀ (w : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) w),
        E (ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b)) = ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (e w b))) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (z : ℬ.Points (AlgebraicClosure ℚ)), E (τ • z) = τ • E z) := by
    refine ⟨AddMonoidHom.toAddEquiv Efwd Ebwd hEE₁ hEE₂, hEfwd, fun τ z => ?_⟩
    exact PDivisibleGroup.pointsLift_smul ℬ ℬ₀ (AlgebraicClosure ℚ) _ hecompat hegal τ z
  obtain ⟨E, hEb, hEgal⟩ := P2

  have P3 : ∃ Φ₀ : 𝒢.Points (AlgebraicClosure ℚ) →+ ℬ₀.Points (AlgebraicClosure ℚ),
      (∀ (w : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) w),
        Φ₀ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul x)) = ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w
          (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ₀ w : ℬ₀.level w →ₐ[Rh] 𝒢.level w))))) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (z : 𝒢.Points (AlgebraicClosure ℚ)), Φ₀ (τ • z) = τ • Φ₀ z) :=
    ⟨PDivisibleGroup.pointsLift 𝒢 ℬ₀ (AlgebraicClosure ℚ) Φ₀ hΦ₀incl,
      fun w x => PDivisibleGroup.pointsLift_mkAdd 𝒢 ℬ₀ (AlgebraicClosure ℚ) Φ₀ hΦ₀incl w x,
      PDivisibleGroup.pointsLift_smul 𝒢 ℬ₀ (AlgebraicClosure ℚ) Φ₀ hΦ₀incl hΦ₀gal'⟩
  obtain ⟨Φ₀, hΦ₀, hΦ₀gal⟩ := P3

  have hElev : ∀ (w : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) w), ∃ b₀ : ℬ₀.Point (AlgebraicClosure ℚ) w,
      (E : ℬ.Points (AlgebraicClosure ℚ) →+ ℬ₀.Points (AlgebraicClosure ℚ)) (ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b)) =
        ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b₀) := fun w b => ⟨e w b, hEb w b⟩
  obtain ⟨θ, -, hθpts, -⟩ :=
    PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
      p Pl hPl Rh hRA hRloc hres ℬ ℬ₀ (E : ℬ.Points (AlgebraicClosure ℚ) →+ ℬ₀.Points (AlgebraicClosure ℚ)) hElev hEgal
  have hE'lev : ∀ (w : ℕ) (b₀ : ℬ₀.Point (AlgebraicClosure ℚ) w), ∃ b : ℬ.Point (AlgebraicClosure ℚ) w,
      (E.symm : ℬ₀.Points (AlgebraicClosure ℚ) →+ ℬ.Points (AlgebraicClosure ℚ)) (ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b₀)) =
        ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b) := fun w b₀ =>
    ⟨(e w).symm b₀, (AddEquiv.symm_apply_eq E).2 (by rw [hEb, MulEquiv.apply_symm_apply])⟩
  have hE'gal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (z : ℬ₀.Points (AlgebraicClosure ℚ)), E.symm (τ • z) = τ • E.symm z := by
    intro τ z
    apply E.injective
    rw [AddEquiv.apply_symm_apply, hEgal, AddEquiv.apply_symm_apply]
  obtain ⟨θ', -, hθ'pts, -⟩ :=
    PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
      p Pl hPl Rh hRA hRloc hres ℬ₀ ℬ (E.symm : ℬ₀.Points (AlgebraicClosure ℚ) →+ ℬ.Points (AlgebraicClosure ℚ)) hE'lev hE'gal

  obtain ⟨φB, -, -, huniqB⟩ :=
    PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
      p Pl hPl Rh hRA hRloc hres ℬ ℬ (AddMonoidHom.id (ℬ.Points (AlgebraicClosure ℚ))) (fun w b => ⟨b, rfl⟩) (fun τ z => rfl)
  have hid : (fun w => (θ w).comp (θ' w)) = fun w => BialgHom.id Rh (ℬ.level w) := by
    refine (huniqB _ ?_).trans (huniqB _ ?_).symm
    · intro w b
      calc AddMonoidHom.id (ℬ.Points (AlgebraicClosure ℚ)) (ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b))
          = E.symm (E (ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul b))) := (AddEquiv.symm_apply_apply E _).symm
        _ = E.symm (ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom b).comp (θ w : ℬ₀.level w →ₐ[Rh] ℬ.level w))))) :=
              congrArg E.symm (hθpts w b)
        _ = _ := hθ'pts w _
    · intro w b
      rfl

  obtain ⟨φ0, -, -, huniq0⟩ :=
    PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
      p Pl hPl Rh hRA hRloc hres 𝒢 ℬ₀ Φ₀ (fun w x => ⟨_, hΦ₀ w x⟩) hΦ₀gal
  have hcomp : (fun w => (ψ w).comp (θ w)) = ψ₀ := by
    refine (huniq0 _ ?_).trans (huniq0 ψ₀ hΦ₀).symm
    intro w x
    calc Φ₀ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul x))
        = ℬ₀.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (e w (Φ w x))) := by rw [hΦ₀, he]; rfl
      _ = E (ℬ.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (Φ w x))) := (hEb w _).symm
      _ = _ := hθpts w _

  obtain ⟨r₀, hr₀v⟩ := hr₀ v
  refine ⟨(θ v : ℬ₀.level v →ₐc[Rh] ℬ.level v).toLinearMap.comp r₀, fun b => ?_⟩
  have h1 : ψ v b = ψ₀ v (θ' v b) := by
    have := congrFun hcomp v
    rw [← this]
    show ψ v b = ψ v (θ v (θ' v b))
    rw [show θ v (θ' v b) = ((θ v).comp (θ' v)) b from rfl, show (θ v).comp (θ' v) = BialgHom.id Rh (ℬ.level v) from congrFun hid v]
    rfl
  show θ v (r₀ (ψ v b)) = b
  rw [h1, hr₀v, show θ v (θ' v b) = ((θ v).comp (θ' v)) b from rfl,
    show (θ v).comp (θ' v) = BialgHom.id Rh (ℬ.level v) from congrFun hid v]
  rfl

end S_PDivisibleGroup_exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime
end P2MW
export P2MW.S_PDivisibleGroup_exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime (solution)
