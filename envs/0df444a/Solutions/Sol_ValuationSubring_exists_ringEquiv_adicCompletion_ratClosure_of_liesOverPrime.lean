-- Prove2me | solution 1 for ValuationSubring.exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/48be4e4b-a488-55c2-9461-89ca0b8472ab

import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField ValuationSubring P2MW.S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime.ValuationSubring"

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype ext mem_nonunits_iff ValueGroup valuation_le_one_iff valuation ratClosure isClosed_ratClosure coe_ratClosure coe_ratCast_mem_ratClosure LiesOverPrime mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one"
namespace ISOkit
p2m_open "ValuationSubring"

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

noncomputable def wQ : Valuation ℚ A.ValueGroup := A.valuation.comap (algebraMap ℚ (AlgebraicClosure ℚ))

theorem wQ_apply (q : ℚ) : wQ A q = A.valuation (q : AlgebraicClosure ℚ) := by
  show A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) q) = _
  rw [eq_ratCast]

theorem vA_natCast_le_one (n : ℕ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (natCast_mem A n)

theorem vA_intCast_le_one (n : ℤ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

theorem vA_natCast_eq_one_of_coprime (hA : A.LiesOverPrime r) {d : ℕ} (hd : d.Coprime r) :
    A.valuation (d : AlgebraicClosure ℚ) = 1 := by
  refine le_antisymm (vA_natCast_le_one A d) (not_lt.mp fun hlt => ?_)
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  obtain ⟨u, t, hut⟩ := Nat.isCoprime_iff_coprime.mpr hd
  have h1 : (u : AlgebraicClosure ℚ) * d + t * r = 1 := by exact_mod_cast hut
  have hv : A.valuation ((u : AlgebraicClosure ℚ) * d + t * r) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (vA_intCast_le_one A u) zero_le' hlt
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (vA_intCast_le_one A t) zero_le' hAr
  rw [h1, map_one] at hv
  exact lt_irrefl _ hv

theorem vA_ratCast_le_one_iff (hr : r.Prime) (hA : A.LiesOverPrime r) (q : ℚ) :
    A.valuation (q : AlgebraicClosure ℚ) ≤ 1 ↔ ¬ r ∣ q.den := by
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have hden0 : A.valuation (q.den : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr (by exact_mod_cast q.den_nz)
  constructor
  · intro hq hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hden : A.valuation (q.den : AlgebraicClosure ℚ) < 1 := by
      rw [hk, Nat.cast_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hAr (vA_natCast_le_one A k)
    have hnum : (q.num.natAbs).Coprime r := Nat.Coprime.coprime_dvd_right ⟨k, hk⟩ q.reduced
    have hvnum : A.valuation (q.num : AlgebraicClosure ℚ) = 1 := by
      have h := vA_natCast_eq_one_of_coprime A hA hnum
      have hcast : ((q.num.natAbs : ℕ) : AlgebraicClosure ℚ) = ((q.num.natAbs : ℤ) : AlgebraicClosure ℚ) :=
        (Int.cast_natCast _).symm
      rcases Int.natAbs_eq q.num with hn | hn
      · rw [hn, ← hcast]; exact h
      · rw [hn, Int.cast_neg, Valuation.map_neg, ← hcast]; exact h
    have hq' : A.valuation (q : AlgebraicClosure ℚ) = (A.valuation (q.den : AlgebraicClosure ℚ))⁻¹ := by
      rw [Rat.cast_def, map_div₀, hvnum, one_div]
    rw [hq'] at hq
    have : 1 ≤ A.valuation (q.den : AlgebraicClosure ℚ) := by rwa [inv_le_one₀ (zero_lt_iff.mpr hden0)] at hq
    exact absurd hden (not_lt.mpr this)
  · intro hnd
    have hcop : (q.den).Coprime r := ((Nat.Prime.coprime_iff_not_dvd hr).mpr hnd).symm
    rw [Rat.cast_def, map_div₀, vA_natCast_eq_one_of_coprime A hA hcop, div_one]
    exact vA_intCast_le_one A q.num

theorem natGenerator_eq (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Rat.HeightOneSpectrum.natGenerator v = r := by
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ r := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    rw [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) r]
    exact Ideal.mem_map_of_mem _ hv
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hr).mp hdvd

theorem isEquiv_valuation_wQ (hr : r.Prime) (hA : A.LiesOverPrime r) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : (v.valuation ℚ).IsEquiv (wQ A) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro q
  have hmem : ((q.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ r ∣ q.den := by
    rw [← natGenerator_eq hr v hv, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
      ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) q.den, Ideal.apply_mem_of_equiv_iff]
  rw [Rat.valuation_le_one_iff_den, hmem, wQ_apply, vA_ratCast_le_one_iff A hr hA]

section Bases

variable {R Γ₀ : Type*} [Field R] [LinearOrderedCommGroupWithZero Γ₀] [hR : Valued R Γ₀]

theorem setOf_v_lt_eq_restrict (c : R) :
    {y : R | Valued.v y < Valued.v c} = {y : R | Valued.v.restrict y < Valued.v.restrict c} := by
  ext y
  simp only [Set.mem_setOf_eq]
  rw [← not_le, ← not_le, Valuation.restrict_le_iff]

theorem hasBasis_nhds_zero_elt :
    (nhds (0 : R)).HasBasis (fun c : R => Valued.v c ≠ 0) (fun c => {y : R | Valued.v y < Valued.v c}) := by
  refine (Valued.hasBasis_nhds_zero R Γ₀).to_hasBasis (fun γ _ => ?_) (fun c hc => ?_)
  · obtain ⟨a, b, ha, hb, hab⟩ := hR.v.restrict_exists_div_eq γ
    refine ⟨a / b, ?_, ?_⟩
    · rw [map_div₀]; exact div_ne_zero ha.ne' hb.ne'
    · rw [setOf_v_lt_eq_restrict, map_div₀, hab]
  · have hc' : hR.v.restrict c ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mp hc)
    refine ⟨Units.mk0 _ hc', trivial, fun y hy => ?_⟩
    rw [setOf_v_lt_eq_restrict]
    rw [Set.mem_setOf_eq, Units.val_mk0] at hy
    exact hy

theorem hasBasis_uniformity_elt :
    (uniformity R).HasBasis (fun c : R => Valued.v c ≠ 0)
      (fun c => {p : R × R | Valued.v (p.2 - p.1) < Valued.v c}) := by
  rw [uniformity_eq_comap_nhds_zero]
  exact hasBasis_nhds_zero_elt.comap _

end Bases

section Iota

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

noncomputable def iota : WithVal (wQ A) →+* WithVal A.valuation :=
  WithVal.map (wQ A) A.valuation (algebraMap ℚ (AlgebraicClosure ℚ))

theorem v_iota (x : WithVal (wQ A)) : Valued.v (iota A x) = Valued.v x := rfl

theorem iota_apply_ofVal (x : WithVal (wQ A)) :
    (iota A x).ofVal = algebraMap ℚ (AlgebraicClosure ℚ) x.ofVal := rfl

theorem uniformContinuous_iota (hr : r.Prime) (hA : A.LiesOverPrime r) [MulArchimedean A.ValueGroup] :
    UniformContinuous (iota A) := by
  refine uniformContinuous_addMonoidHom_of_continuous (f := (iota A : WithVal (wQ A) →+ WithVal A.valuation)) ?_
  refine continuous_of_continuousAt_zero (iota A : WithVal (wQ A) →+ WithVal A.valuation) ?_
  rw [ContinuousAt, map_zero]
  refine (hasBasis_nhds_zero_elt.tendsto_iff hasBasis_nhds_zero_elt).mpr fun c' hc' => ?_

  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have hvr0 : 0 < A.valuation (r : AlgebraicClosure ℚ) :=
    zero_lt_iff.mpr ((map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero))
  obtain ⟨n, hn⟩ := MulArchimedean.arch (Valued.v c')⁻¹ ((one_lt_inv₀ hvr0).mpr hAr)
  rw [inv_pow] at hn
  have hn' : A.valuation (r : AlgebraicClosure ℚ) ^ n ≤ Valued.v c' :=
    (inv_le_inv₀ (zero_lt_iff.mpr hc') (pow_pos hvr0 n)).mp hn
  refine ⟨WithVal.toVal (wQ A) ((r : ℚ) ^ n), ?_, fun y hy => ?_⟩
  · show wQ A ((r : ℚ) ^ n) ≠ 0
    rw [map_pow, wQ_apply, Rat.cast_natCast]; exact pow_ne_zero _ hvr0.ne'
  · show Valued.v (iota A y) < Valued.v c'
    rw [v_iota]
    refine lt_of_lt_of_le hy ?_
    show wQ A ((r : ℚ) ^ n) ≤ _
    rw [map_pow, wQ_apply, Rat.cast_natCast]; exact hn'

theorem isUniformInducing_iota (hr : r.Prime) (hA : A.LiesOverPrime r) [MulArchimedean A.ValueGroup] :
    IsUniformInducing (iota A) := by
  refine ⟨le_antisymm ?_ (uniformContinuous_iff.mp (uniformContinuous_iota A hr hA))⟩
  refine (hasBasis_uniformity_elt.comap _).le_basis_iff hasBasis_uniformity_elt |>.mpr fun c hc => ?_
  refine ⟨iota A c, by rw [v_iota]; exact hc, fun p hp => ?_⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
  rw [← map_sub, v_iota, v_iota] at hp
  exact hp

end Iota

section Ext

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

theorem eq_of_isClopen_of_dense {X : Type*} [TopologicalSpace X] {U V D : Set X} (hU : IsClopen U) (hV : IsClopen V)
    (hD : Dense D) (h : ∀ x ∈ D, x ∈ U ↔ x ∈ V) : U = V := by
  ext z
  constructor
  · intro hzU
    by_contra hzV
    obtain ⟨x, hxD, hxU, hxV⟩ := hD.exists_mem_open (hU.isOpen.inter hV.compl.isOpen) ⟨z, hzU, hzV⟩
    exact hxV ((h x hxD).mp hxU)
  · intro hzV
    by_contra hzU
    obtain ⟨x, hxD, hxV, hxU⟩ := hD.exists_mem_open (hV.isOpen.inter hU.compl.isOpen) ⟨z, hzV, hzU⟩
    exact hxU ((h x hxD).mpr hxV)

noncomputable def fQ : WithVal (wQ A) →+* A.valuation.Completion :=
  (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion).comp (iota A)

theorem fQ_apply (k : WithVal (wQ A)) : fQ A k = ((iota A k : WithVal A.valuation) : A.valuation.Completion) := rfl

theorem fQ_toVal (q : ℚ) : fQ A (WithVal.toVal (wQ A) q) = ((q : AlgebraicClosure ℚ) : A.valuation.Completion) := by
  rw [fQ_apply]
  show (((WithVal.toVal A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) q)) : WithVal A.valuation) : A.valuation.Completion) = _
  rw [eq_ratCast]
  rfl

variable (hr : r.Prime) (hA : A.LiesOverPrime r) [MulArchimedean A.ValueGroup]
include hr hA

theorem continuous_fQ : Continuous (fQ A) :=
  UniformSpace.Completion.continuous_coeRingHom.comp (uniformContinuous_iota A hr hA).continuous

theorem isUniformInducing_fQ : IsUniformInducing (fQ A) :=
  (UniformSpace.Completion.isUniformInducing_coe _).comp (isUniformInducing_iota A hr hA)

noncomputable def ehat : (wQ A).Completion →+* A.valuation.Completion :=
  UniformSpace.Completion.extensionHom (fQ A) (continuous_fQ A hr hA)

theorem ehat_coe (k : WithVal (wQ A)) : ehat A hr hA (k : (wQ A).Completion) = fQ A k :=
  UniformSpace.Completion.extensionHom_coe (fQ A) (continuous_fQ A hr hA) k

theorem isUniformInducing_ehat : IsUniformInducing (ehat A hr hA) := by
  show IsUniformInducing (UniformSpace.Completion.extension (fQ A))
  exact UniformSpace.Completion.isUniformInducing_extension (isUniformInducing_fQ A hr hA)

theorem continuous_ehat : Continuous (ehat A hr hA) := (isUniformInducing_ehat A hr hA).uniformContinuous.continuous

theorem injective_ehat : Function.Injective (ehat A hr hA) := (isUniformInducing_ehat A hr hA).injective

theorem isClosed_range_ehat : IsClosed (Set.range (ehat A hr hA)) :=
  (isUniformInducing_ehat A hr hA).isComplete_range.isClosed

theorem range_ehat : Set.range (ehat A hr hA) = (ratClosure A : Set A.valuation.Completion) := by
  apply le_antisymm
  ·
    refine ((continuous_ehat A hr hA).range_subset_closure_image_dense UniformSpace.Completion.denseRange_coe).trans ?_
    refine closure_minimal ?_ (isClosed_ratClosure A)
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [ehat_coe, show k = WithVal.toVal (wQ A) k.ofVal from rfl, fQ_toVal]
    exact coe_ratCast_mem_ratClosure A _
  ·
    rw [coe_ratClosure]
    refine closure_minimal ?_ (isClosed_range_ehat A hr hA)
    intro x hx
    have : (⊥ : Subfield A.valuation.Completion) ≤ (Rat.castHom A.valuation.Completion).fieldRange := bot_le
    obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.mp (this hx)
    refine ⟨(WithVal.toVal (wQ A) q : (wQ A).Completion), ?_⟩
    rw [ehat_coe, fQ_toVal, ← hq]
    show _ = (q : A.valuation.Completion)
    show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
        ((WithVal.equiv A.valuation).symm (q : AlgebraicClosure ℚ)) = _
    rw [map_ratCast, map_ratCast]

theorem v_le_one_iff_ehat (z : (wQ A).Completion) : Valued.v z ≤ 1 ↔ Valued.v (ehat A hr hA z) ≤ 1 := by
  have key : {z : (wQ A).Completion | Valued.v z ≤ 1} = {z | Valued.v (ehat A hr hA z) ≤ 1} := by
    refine eq_of_isClopen_of_dense ?_ ?_ UniformSpace.Completion.denseRange_coe ?_
    · have : {z : (wQ A).Completion | Valued.v z ≤ 1} = {z | Valued.v.restrict z ≤ 1} := by
        ext z; simp only [Set.mem_setOf_eq, Valuation.restrict_le_one_iff]
      rw [this]; exact Valued.isClopen_closedBall _ (r := 1) one_ne_zero
    · have : {z : (wQ A).Completion | Valued.v (ehat A hr hA z) ≤ 1} =
          (ehat A hr hA) ⁻¹' {w : A.valuation.Completion | Valued.v.restrict w ≤ 1} := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.restrict_le_one_iff]
      rw [this]; exact (Valued.isClopen_closedBall _ (r := 1) one_ne_zero).preimage (continuous_ehat A hr hA)
    · rintro _ ⟨k, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [ehat_coe, fQ_apply, Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, v_iota]
  exact Set.ext_iff.mp key z

end Ext

section Assembly

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ} (hr : r.Prime) (hA : A.LiesOverPrime r) [MulArchimedean A.ValueGroup]
include hr hA

noncomputable def e₂ : (wQ A).Completion ≃+* ↥(ratClosure A) :=
  RingEquiv.ofBijective
    ((ehat A hr hA).codRestrict (ratClosure A) fun z => by
      rw [← SetLike.mem_coe, ← range_ehat A hr hA]; exact ⟨z, rfl⟩)
    ⟨fun x y h => injective_ehat A hr hA (congrArg Subtype.val h), fun y => by
      obtain ⟨z, hz⟩ := (Set.ext_iff.mp (range_ehat A hr hA) (y : A.valuation.Completion)).mpr y.2
      exact ⟨z, Subtype.ext hz⟩⟩

theorem coe_e₂ (z : (wQ A).Completion) : ((e₂ A hr hA z : ↥(ratClosure A)) : A.valuation.Completion) = ehat A hr hA z := rfl

theorem continuous_e₂ : Continuous (e₂ A hr hA) :=
  (continuous_ehat A hr hA).subtype_mk _

theorem continuous_e₂_symm : Continuous (e₂ A hr hA).symm := by
  rw [(isUniformInducing_ehat A hr hA).isInducing.continuous_iff]
  have : (ehat A hr hA) ∘ (e₂ A hr hA).symm = Subtype.val := by
    funext y
    show ((e₂ A hr hA ((e₂ A hr hA).symm y) : ↥(ratClosure A)) : A.valuation.Completion) = y
    rw [RingEquiv.apply_symm_apply]
  rw [this]; exact continuous_subtype_val

end Assembly

end ValuationSubring.ISOkit

open ValuationSubring.ISOkit in

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ e : v.adicCompletion ℚ ≃+* ↥(ratClosure A),
      (∀ q : ℚ, ((e (algebraMap ℚ (v.adicCompletion ℚ) q) : ↥(ratClosure A)) : A.valuation.Completion) =
        ((q : AlgebraicClosure ℚ) : A.valuation.Completion)) ∧
      (∀ x : v.adicCompletion ℚ,
        x ∈ v.adicCompletionIntegers ℚ ↔ e x ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring) ∧
      Continuous e ∧ Continuous e.symm := by
  classical
  have hrp : r.Prime := Fact.out
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ; rfl; rfl
  haveI : MulArchimedean A.ValueGroup :=
    ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one A hrp hAr

  have hEq := isEquiv_valuation_wQ A hrp hA v hv
  let g : WithVal (v.valuation ℚ) ≃+* WithVal (wQ A) := WithVal.congr (v.valuation ℚ) (wQ A) (RingEquiv.refl ℚ)
  have hg : Continuous g := hEq.uniformEquiv.continuous
  have hg' : Continuous g.symm := hEq.uniformEquiv.symm.continuous
  let e₁ : v.adicCompletion ℚ ≃+* (wQ A).Completion :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv ℚ v).trans
      (UniformSpace.Completion.mapRingEquiv g hg hg')
  have he₁ : ∀ x, e₁ x = UniformSpace.Completion.map g x.toCompletion := fun x => rfl
  have he₁symm : ∀ y, e₁.symm y =
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map g.symm y) :=
    fun y => rfl
  have hgu : UniformContinuous g := hEq.uniformEquiv.uniformContinuous

  refine ⟨e₁.trans (e₂ A hrp hA), fun q => ?_, fun x => ?_, ?_, ?_⟩
  ·
    rw [RingEquiv.trans_apply, coe_e₂]
    try simp only [Function.comp_apply]
    rw [he₁, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion,
      UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.map_coe hgu, ehat_coe]
    first
      | exact fQ_toVal A q
      | (simp only [eq_ratCast]; exact fQ_toVal A q)
  ·
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, RingEquiv.trans_apply, Valuation.mem_valuationSubring_iff,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuedAdicCompletion_def]
    change Valued.v x.toCompletion ≤ 1 ↔ _
    rw [hEq.valuedCompletion_le_one_iff]
    show Valued.v (e₁ x) ≤ 1 ↔ Valued.v (ehat A hrp hA (e₁ x)) ≤ 1
    exact v_le_one_iff_ehat A hrp hA _
  ·
    exact (continuous_e₂ A hrp hA).comp (UniformSpace.Completion.continuous_map.comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion (K := ℚ) (v := v)))
  ·
    show Continuous (fun y => e₁.symm ((e₂ A hrp hA).symm y))
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion (K := ℚ) (v := v)).comp
      (UniformSpace.Completion.continuous_map.comp (continuous_e₂_symm A hrp hA))

end S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime (solution)
