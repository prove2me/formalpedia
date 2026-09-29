-- Prove2me | solution 1 for WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed_of_charP_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/04ac579d-ef2c-59df-a48f-fe70623e99b0

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_isSeparable
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental
import Theorems.Thm_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField
import Theorems.Thm_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

noncomputable section

open Polynomial IntermediateField AlgebraicCurve

namespace W8O

section Tower

variable {K F M E : Type*} [Field K] [Field F] [Field M] [Field E]
  [Algebra K F] [Algebra K M] [Algebra K E]
  [Algebra F M] [Algebra M E] [Algebra F E]
  [IsScalarTower K F M] [IsScalarTower K M E] [IsScalarTower K F E] [IsScalarTower F M E]
  [Algebra.IsIntegral F M] [Algebra.IsIntegral M E] [Algebra.IsIntegral F E]

theorem restrict_restrict (w : Place K E) : (w.restrict M).restrict F = w.restrict F := by
  apply Place.ext
  ext f
  change algebraMap M E (algebraMap F M f) ∈ w.toValuationSubring ↔
    algebraMap F E f ∈ w.toValuationSubring
  rw [← IsScalarTower.algebraMap_apply F M E]

theorem inertiaDeg_tower (hdeg : ∀ v : Place K F, v.deg ≠ 0) (w : Place K E) :
    (w.restrict M).inertiaDeg F * w.inertiaDeg M = w.inertiaDeg F := by
  have h1 := Place.deg_restrict_mul_inertiaDeg (F := F) w
  have h2 := Place.deg_restrict_mul_inertiaDeg (F := M) w
  have h3 := Place.deg_restrict_mul_inertiaDeg (F := F) (w.restrict M)
  rw [restrict_restrict] at h3
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hdeg (w.restrict F))) ?_
  rw [h1, ← h2, ← h3, mul_assoc]

theorem pushforward_pushforward
    (hf : ∀ w : Place K E, (w.restrict M).inertiaDeg F * w.inertiaDeg M = w.inertiaDeg F)
    (D : Divisor K E) :
    Divisor.pushforward F (Divisor.pushforward M D) = Divisor.pushforward F D := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g h₁ h₂ => simp only [map_add, h₁, h₂]
  | single w n =>
    rw [Divisor.pushforward_single, Divisor.pushforward_single, Divisor.pushforward_single,
      restrict_restrict, ← hf w, Nat.cast_mul]
    congr 1
    ring

theorem normFormula_trans [Module.Finite F M] [Module.Finite M E] [Module.Finite F E]
    (hf : ∀ w : Place K E, (w.restrict M).inertiaDeg F * w.inertiaDeg M = w.inertiaDeg F)
    (hME : Divisor.PushforwardNormFormula K M E)
    (hFM : Divisor.PushforwardNormFormula K F M) :
    Divisor.PushforwardNormFormula K F E := by
  intro f hf0 D hD v
  rw [← pushforward_pushforward hf D, ← Algebra.norm_norm (R := F) (S := M) (a := f)]
  exact hFM (Algebra.norm M f) (Algebra.norm_ne_zero_iff.2 hf0) (Divisor.pushforward M D)
    (fun u => hME f hf0 D hD u) v

end Tower

theorem pow_mem_valuationSubring_iff {E : Type*} [Field E] (O : ValuationSubring E) {n : ℕ}
    (hn : n ≠ 0) (u : E) : u ^ n ∈ O ↔ u ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

theorem ord_npow {K E : Type*} [Field K] [Field E] [Algebra K E] (w : Place K E) (x : E)
    (n : ℕ) : w.ord (x ^ n) = (n : ℤ) * w.ord x := by
  rw [← zpow_natCast, Place.ord_zpow]

section PurelyInseparable

variable {K M E : Type*} [Field K] [Field M] [Field E]
  [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
  [FiniteDimensional M E] [IsPurelyInseparable M E]
  (p : ℕ) [Fact p.Prime] [CharP E p] [CharP M p] {r : ℕ}
  (hrange : (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange)

include hrange in
theorem exponent_le : IsPurelyInseparable.exponent M E ≤ r := by
  by_contra h
  obtain ⟨a, ha⟩ := IsPurelyInseparable.exponent_min' (K := M) (L := E) p (not_le.1 h)
  apply ha
  have : a ^ p ^ r ∈ (algebraMap M E).fieldRange := by
    rw [hrange]
    exact RingHom.mem_fieldRange.2 ⟨a, by rw [iterateFrobenius_def]⟩
  exact RingHom.mem_range.2 (RingHom.mem_fieldRange.1 this)

def theta : E →+* M := IsPurelyInseparable.iterateFrobenius M E p (exponent_le p hrange)

theorem algebraMap_theta (x : E) : algebraMap M E (theta p hrange x) = x ^ p ^ r :=
  IsPurelyInseparable.algebraMap_iterateFrobenius M p _ x

theorem theta_algebraMap (m : M) : theta p hrange (algebraMap M E m) = m ^ p ^ r :=
  IsPurelyInseparable.iterateFrobenius_algebraMap E p _ m

theorem theta_surjective : Function.Surjective (theta p hrange) := by
  intro m
  have hm : algebraMap M E m ∈ (iterateFrobenius E p r).fieldRange := by
    rw [← hrange]; exact RingHom.mem_fieldRange.2 ⟨m, rfl⟩
  obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 hm
  refine ⟨x, (algebraMap M E).injective ?_⟩
  rw [algebraMap_theta, ← hx, iterateFrobenius_def]

theorem theta_ne_zero {x : E} (hx : x ≠ 0) : theta p hrange x ≠ 0 :=
  (_root_.map_ne_zero (theta p hrange)).2 hx

theorem pow_ne : p ^ r ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero

def liftPlace (v : Place K M) : Place K E where
  toValuationSubring := v.toValuationSubring.comap (theta p hrange)
  algebraMap_mem' k := by
    rw [ValuationSubring.mem_comap, IsScalarTower.algebraMap_apply K M E, theta_algebraMap]
    exact pow_mem (v.algebraMap_mem' k) _
  ne_top' h := v.ne_top' (eq_top_iff.2 fun m _ => by
    obtain ⟨x, rfl⟩ := theta_surjective p hrange m
    exact ValuationSubring.mem_comap.1 (h ▸ ValuationSubring.mem_top x))
  isPrincipalIdealRing' := by

    set O' : ValuationSubring E := v.toValuationSubring.comap (theta p hrange)
    let ψ : O' →+* v.toValuationSubring :=
      ((theta p hrange).comp O'.subtype).codRestrict v.toValuationSubring.toSubring
        fun x => ValuationSubring.mem_comap.1 x.2
    have hψ : Function.Bijective ψ := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        apply (theta p hrange).injective
        exact congrArg Subtype.val hxy
      · intro y
        obtain ⟨x, hx⟩ := theta_surjective p hrange (y : M)
        refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
        change x ∈ O'
        rw [ValuationSubring.mem_comap, hx]; exact y.2
    exact IsPrincipalIdealRing.of_surjective (RingEquiv.ofBijective ψ hψ).symm.toRingHom
      (RingEquiv.ofBijective ψ hψ).symm.surjective

theorem mem_liftPlace_iff (v : Place K M) (x : E) :
    x ∈ (liftPlace p hrange v).toValuationSubring ↔ theta p hrange x ∈ v.toValuationSubring :=
  ValuationSubring.mem_comap

theorem restrict_liftPlace (v : Place K M) : (liftPlace p hrange v).restrict M = v := by
  apply Place.ext
  ext m
  rw [Place.mem_restrict_iff, mem_liftPlace_iff, theta_algebraMap]
  exact pow_mem_valuationSubring_iff _ (pow_ne p) m

theorem eq_liftPlace_of_restrict_eq {w : Place K E} {v : Place K M} (h : w.restrict M = v) :
    w = liftPlace p hrange v := by
  subst h
  apply Place.ext
  ext x
  rw [mem_liftPlace_iff, Place.mem_restrict_iff, algebraMap_theta]
  exact (pow_mem_valuationSubring_iff _ (pow_ne p) x).symm

theorem restrict_eq_iff (w : Place K E) (v : Place K M) :
    w.restrict M = v ↔ w = liftPlace p hrange v :=
  ⟨eq_liftPlace_of_restrict_eq p hrange, fun h => h ▸ restrict_liftPlace p hrange v⟩

include hrange in
omit [Algebra K M] [IsScalarTower K M E] in

theorem ramificationIndex_eq (w : Place K E) : w.ramificationIndex M = p ^ r := by
  have hprime : p.Prime := Fact.out
  apply le_antisymm
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    have hπ0 : (π : E) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    have hθπ0 : theta p hrange (π : E) ≠ 0 := theta_ne_zero p hrange hπ0
    have hord : w.ord (algebraMap M E (theta p hrange (π : E))) = (p ^ r : ℕ) := by
      rw [algebraMap_theta, ord_npow, w.ord_coe_irreducible hπ, mul_one]
    have := Place.ramificationIndex_le_ord (F := M) w hθπ0
      (by rw [hord]; exact_mod_cast pow_pos hprime.pos r)
    rw [hord] at this
    exact_mod_cast this
  · obtain ⟨m, hm0, hm⟩ := Place.exists_ord_eq_ramificationIndex (F := M) w
    obtain ⟨x, rfl⟩ := theta_surjective p hrange m
    rw [algebraMap_theta, ord_npow] at hm
    have hpos := Place.ramificationIndex_pos (F := M) w

    have hx1 : 1 ≤ w.ord x := by
      by_contra hlt
      have : (↑(p ^ r) : ℤ) * w.ord x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      omega
    have : (↑(p ^ r) : ℤ) * 1 ≤ ↑(p ^ r) * w.ord x :=
      mul_le_mul_of_nonneg_left hx1 (by positivity)
    have h' : ((p ^ r : ℕ) : ℤ) ≤ (w.ramificationIndex M : ℤ) := by rw [← hm]; linarith
    exact_mod_cast h'

omit [CharP E p] in

theorem algebraMap_norm (hq : Module.finrank M E = p ^ r) (f : E) :
    algebraMap M E (Algebra.norm M f) = f ^ p ^ r := by
  have hprime : p.Prime := Fact.out
  haveI : ExpChar M p := ExpChar.prime hprime
  have hint : IsIntegral M f := IsIntegral.of_finite M f
  obtain ⟨n, y, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C M p f

  have hgen : Algebra.norm M (AdjoinSimple.gen M f) = y := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hint)
    rw [adjoin.powerBasis_gen, adjoin.powerBasis_dim, minpoly_gen, hmin,
      natDegree_X_pow_sub_C, neg_one_pow_expChar_pow, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_zero,
      if_neg (Ne.symm (pow_ne_zero n hprime.ne_zero)), zero_sub, neg_mul_neg, one_mul] at h
    exact h

  have hfy : f ^ p ^ n = algebraMap M E y := by
    have := minpoly.aeval M f
    rw [hmin, map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at this
    exact this

  have hdegf : Module.finrank M M⟮f⟯ = p ^ n := by
    rw [adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]
  have htower := Module.finrank_mul_finrank M M⟮f⟯ E
  rw [Algebra.norm_eq_norm_adjoin M f, hgen, map_pow, ← hfy, ← pow_mul, ← hdegf, htower, hq]

omit [FiniteDimensional M E] [IsPurelyInseparable M E] in

theorem inertiaDeg_eq_one [Algebra.IsIntegral M E] (hdeg : ∀ w : Place K E, w.deg = 1)
    (w : Place K E) : w.inertiaDeg M = 1 := by
  have h := Place.deg_restrict_mul_inertiaDeg (F := M) w
  rw [hdeg] at h
  exact Nat.eq_one_of_mul_eq_one_left h

include hrange in

theorem pushforward_apply_PI (hdeg : ∀ w : Place K E, w.deg = 1) (D : Divisor K E)
    (v : Place K M) : Divisor.pushforward M D v = D (liftPlace p hrange v) := by
  classical
  rw [Divisor.pushforward_apply, Finset.sum_eq_single (liftPlace p hrange v)]
  · rw [if_pos (restrict_liftPlace p hrange v), inertiaDeg_eq_one hdeg, Nat.cast_one, mul_one]
  · intro w _ hne
    rw [if_neg]
    exact fun h => hne (eq_liftPlace_of_restrict_eq p hrange h)
  · intro hnot
    rw [Finsupp.mem_support_iff, not_not] at hnot
    rw [hnot, zero_mul, ite_self]

include hrange in

theorem ord_liftPlace_algebraMap (v : Place K M) (g : M) :
    (liftPlace p hrange v).ord (algebraMap M E g) = ((p ^ r : ℕ) : ℤ) * v.ord g := by
  have h := Place.ord_restrict (F := M) (liftPlace p hrange v) g
  rwa [restrict_liftPlace, ramificationIndex_eq p hrange] at h

include hrange in

theorem normFormula_PI (hq : Module.finrank M E = p ^ r) (hdeg : ∀ w : Place K E, w.deg = 1) :
    Divisor.PushforwardNormFormula K M E := by
  intro f hf0 D hD v
  rw [pushforward_apply_PI p hrange hdeg, hD]

  have h1 := ord_liftPlace_algebraMap p hrange v (Algebra.norm M f)
  rw [algebraMap_norm p hq, ord_npow] at h1
  exact mul_left_cancel₀ (by exact_mod_cast pow_ne (r := r) p) h1

include p hrange in

theorem hasPrincipalDivisors_PI [HasPrincipalDivisors K E] (hdeg : ∀ w : Place K E, w.deg = 1) :
    HasPrincipalDivisors K M := by
  classical
  refine ⟨fun g hg0 => ?_⟩
  have hg0' : algebraMap M E g ≠ 0 := (_root_.map_ne_zero _).2 hg0
  obtain ⟨DE, hDE, hdegDE⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (algebraMap M E g) hg0'
  have hpr : ((p ^ r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne (r := r) p

  have hfin : (Function.support fun v : Place K M => v.ord g).Finite := by
    refine (DE.support.finite_toSet.image (fun w : Place K E => w.restrict M)).subset ?_
    intro v hv
    refine ⟨liftPlace p hrange v, ?_, restrict_liftPlace p hrange v⟩
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hDE, ord_liftPlace_algebraMap p hrange]
    exact mul_ne_zero hpr hv
  let D : Divisor K M := Finsupp.ofSupportFinite _ hfin
  have hD : ∀ v, D v = v.ord g := fun v => rfl
  refine ⟨D, hD, ?_⟩

  have hpush : Divisor.pushforward M DE = ((p ^ r : ℕ) : ℤ) • D := by
    ext v
    rw [pushforward_apply_PI p hrange hdeg, Finsupp.smul_apply, smul_eq_mul, hD, hDE,
      ord_liftPlace_algebraMap p hrange]
  have h := Divisor.degree_pushforward (F := M) DE
  rw [hdegDE, hpush, map_zsmul, smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hpr

end PurelyInseparable

section Engine

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  (p : ℕ) [Fact p.Prime] [CharP F' p] [HasPrincipalDivisors K F']

theorem engine_of_tower (S : IntermediateField F F') [Algebra.IsSeparable F S]
    [IsPurelyInseparable S F']
    (hp : Module.finrank (frobenius F' p).fieldRange F' = p)
    (hdegF : ∀ v : Place K F, v.deg = 1) (hdeg : ∀ w : Place K F', w.deg = 1) :
    Divisor.PushforwardNormFormula K F F' := by
  haveI : IsScalarTower K S F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : CharP S p := (Algebra.charP_iff S F' p).2 inferInstance
  obtain ⟨r, hq, hrange⟩ :=
    Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
      (M := S) (E := F') p hp
  have hPI : Divisor.PushforwardNormFormula K S F' := normFormula_PI (K := K) p hrange hq hdeg
  haveI : HasPrincipalDivisors K S := hasPrincipalDivisors_PI (K := K) p hrange hdeg
  have hSep : Divisor.PushforwardNormFormula K F S :=
    AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable
  exact normFormula_trans (M := S)
    (inertiaDeg_tower (fun v => by rw [hdegF v]; exact one_ne_zero)) hPI hSep

theorem engine (hp : Module.finrank (frobenius F' p).fieldRange F' = p)
    (hdegF : ∀ v : Place K F, v.deg = 1) (hdeg : ∀ w : Place K F', w.deg = 1) :
    Divisor.PushforwardNormFormula K F F' :=
  engine_of_tower p (separableClosure F F') hp hdegF hdeg

end Engine

section FunctionField

variable {F : Type*} [Field F] [PerfectField F] (W : WeierstrassCurve.Affine F)
  (p : ℕ) [Fact p.Prime] [CharP F p] [CharP W.FunctionField p]

omit [PerfectField F] in

theorem algebraMap_ratFunc_mem (g : RatFunc F) :
    algebraMap (RatFunc F) W.FunctionField g ∈
      F⟮algebraMap (RatFunc F) W.FunctionField RatFunc.X⟯ := by
  set t := algebraMap (RatFunc F) W.FunctionField RatFunc.X
  have hpoly : ∀ q : F[X],
      algebraMap (RatFunc F) W.FunctionField (algebraMap F[X] (RatFunc F) q) ∈ F⟮t⟯ := by
    intro q
    rw [← RatFunc.aeval_X_left_eq_algebraMap, ← Polynomial.aeval_algebraMap_apply]
    exact IntermediateField.algebra_adjoin_le_adjoin F _ (Polynomial.aeval_mem_adjoin_singleton F _)
  rw [← RatFunc.num_div_denom g, map_div₀]
  exact div_mem (hpoly _) (hpoly _)

theorem finrank_frobenius_functionField :
    Module.finrank (frobenius W.FunctionField p).fieldRange W.FunctionField = p := by
  set t := algebraMap (RatFunc F) W.FunctionField RatFunc.X with ht
  have hinj : Function.Injective (algebraMap (RatFunc F) W.FunctionField) :=
    (algebraMap (RatFunc F) W.FunctionField).injective
  have htr : Transcendental F t := (transcendental_algebraMap_iff hinj).2 RatFunc.transcendental_X

  haveI := WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField W
  let ψ : RatFunc F →+* F⟮t⟯ :=
    (algebraMap (RatFunc F) W.FunctionField).codRestrict F⟮t⟯ (algebraMap_ratFunc_mem W)
  letI : Algebra (RatFunc F) F⟮t⟯ := ψ.toAlgebra
  haveI : IsScalarTower (RatFunc F) F⟮t⟯ W.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional F⟮t⟯ W.FunctionField :=
    Module.Finite.of_restrictScalars_finite (RatFunc F) F⟮t⟯ W.FunctionField
  exact AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental p t htr

end FunctionField

end W8O

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem solution
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (p : ℕ) [CharP F p] [NeZero p]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W] :
    ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin := by
  intro D
  haveI : Fact p.Prime := CharP.char_is_prime_of_pos F p
  haveI : CharP W.FunctionField p :=
    charP_of_injective_algebraMap (algebraMap F W.FunctionField).injective p
  haveI : HasPrincipalDivisors F W.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed W
  have hp := W8O.finrank_frobenius_functionField W p
  have hdeg : ∀ v : Place F W.FunctionField, v.deg = 1 := GenusOnePlaceGate.deg_eq_one
  have hfin : @Module.Finite W.FunctionField W.FunctionField _ _ (algebraAlong D.ι).toModule :=
    D.hfin
  exact @W8O.engine F W.FunctionField W.FunctionField _ _ _ _ _ (algebraAlong D.ι)
    (isScalarTower_along D.ι) hfin p _ _ _ hp hdeg hdeg

end
end S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos
end P2MW
export P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos (solution)
