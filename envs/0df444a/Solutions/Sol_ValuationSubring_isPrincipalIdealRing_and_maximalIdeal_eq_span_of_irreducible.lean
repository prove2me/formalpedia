-- Prove2me | solution 1 for ValuationSubring.isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/76cd54c3-1a92-582e-99da-19d2060e11ba

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible
set_option autoImplicit false

namespace ConstExtCore

open Polynomial IsLocalRing

theorem isDiscreteValuationRing_localization_of_surjective_aeval
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type*} [CommRing D] [IsDomain D] [Algebra O D]
    (hinjD : Function.Injective (algebraMap O D))
    (e : D) (hgen : Function.Surjective (Polynomial.aeval (R := O) e))
    (f : O[X]) (hf : f.Monic) (hfe : aeval e f = 0) (hsep : (f.map (residue O)).Separable)
    (P : Ideal D) [P.IsPrime] (hP : (maximalIdeal O).map (algebraMap O D) ≤ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      maximalIdeal (Localization.AtPrime P) =
        ((maximalIdeal O).map (algebraMap O D)).map (algebraMap D (Localization.AtPrime P)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h𝔪 : maximalIdeal O = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  set 𝔪D : Ideal D := (maximalIdeal O).map (algebraMap O D) with h𝔪D
  have h𝔪D_span : 𝔪D = Ideal.span {algebraMap O D π} := by
    rw [h𝔪D, h𝔪, Ideal.map_span, Set.image_singleton]

  haveI : IsNoetherianRing D := isNoetherianRing_of_surjective O[X] D (Polynomial.aeval e).toRingHom hgen

  set red : O[X] →+* (ResidueField O)[X] := Polynomial.mapRingHom (residue O) with hred
  have hred_surj : Function.Surjective red := Polynomial.map_surjective _ residue_surjective
  have hker𝔪 : ∀ p ∈ RingHom.ker red, aeval e p ∈ 𝔪D := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Polynomial.aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hc : p.coeff i ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff]
      have := congrArg (fun r : (ResidueField O)[X] => r.coeff i) hp
      simpa only [hred, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero] using this
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc)

  set Q : Ideal O[X] := P.comap (Polynomial.aeval e).toRingHom with hQ
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hmemQ : ∀ p : O[X], p ∈ Q ↔ aeval e p ∈ P := fun p => Iff.rfl
  have hker : RingHom.ker red ≤ Q := fun p hp => (hmemQ p).mpr (hP (hker𝔪 p hp))

  set Qb : Ideal (ResidueField O)[X] := Q.map red with hQb
  haveI hQbp : Qb.IsPrime := Ideal.map_isPrime_of_surjective hred_surj hker
  have hfQ : f ∈ Q := by rw [hmemQ, hfe]; exact P.zero_mem
  have hfb0 : red f ≠ 0 := (hf.map (residue O)).ne_zero
  have hfbQ : red f ∈ Qb := Ideal.mem_map_of_mem red hfQ
  have hQb0 : Qb ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hfbQ
    exact hfb0 hfbQ
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal Qb).principal
  have hg' : Qb = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by
    intro h
    apply hQb0
    rw [hg', h, Ideal.span_singleton_eq_bot]
  have hgprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ hQbp)

  have hgf : g ∣ red f := by rw [← Ideal.mem_span_singleton, ← hg']; exact hfbQ
  obtain ⟨h, hfgh⟩ := hgf
  have hgh : ¬ g ∣ h := by
    intro hdvd
    have hsq : Squarefree (red f) := hsep.squarefree
    have hgg : g * g ∣ red f := by rw [hfgh]; exact mul_dvd_mul_left g hdvd
    exact hgprime.not_unit (hsq g hgg)
  have hhQ : h ∉ Qb := by
    intro hh
    rw [hg', Ideal.mem_span_singleton] at hh
    exact hgh hh
  obtain ⟨H, hH⟩ := hred_surj h
  have hHQ : H ∉ Q := by
    intro hHQ'
    exact hhQ (hH ▸ Ideal.mem_map_of_mem red hHQ')
  have hHP : aeval e H ∉ P := fun h' => hHQ ((hmemQ H).mpr h')

  have hclaim : ∀ x ∈ P, aeval e H * x ∈ 𝔪D := by
    intro x hx
    obtain ⟨p, rfl⟩ := hgen x
    have hpQ : p ∈ Q := (hmemQ p).mpr hx
    have hpb : red p ∈ Qb := Ideal.mem_map_of_mem red hpQ
    rw [hg', Ideal.mem_span_singleton] at hpb
    obtain ⟨c, hc⟩ := hpb
    obtain ⟨C, rfl⟩ := hred_surj c
    have hk : H * p - f * C ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_mul, hH, hc, hfgh]
      ring
    have hm := hker𝔪 _ hk
    rwa [map_sub, map_mul, map_mul, hfe, zero_mul, sub_zero] at hm

  have hmaxP : maximalIdeal (Localization.AtPrime P) = P.map (algebraMap D (Localization.AtPrime P)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hB : maximalIdeal (Localization.AtPrime P) = 𝔪D.map (algebraMap D (Localization.AtPrime P)) := by
    apply le_antisymm
    · rw [hmaxP, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have hu : IsUnit (algebraMap D (Localization.AtPrime P) (aeval e H)) :=
        IsLocalization.map_units (Localization.AtPrime P) (⟨aeval e H, hHP⟩ : P.primeCompl)
      have hm : algebraMap D (Localization.AtPrime P) (aeval e H * x) ∈
          𝔪D.map (algebraMap D (Localization.AtPrime P)) := Ideal.mem_map_of_mem _ (hclaim x hx)
      rw [map_mul] at hm
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm
    · rw [hmaxP]
      exact Ideal.map_mono hP

  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl (Localization.AtPrime P) inferInstance
  have hπD0 : algebraMap O D π ≠ 0 := fun h0 => hπ.ne_zero (hinjD (by rw [h0, map_zero]))
  have hinjDL : Function.Injective (algebraMap D (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hπL0 : algebraMap D (Localization.AtPrime P) (algebraMap O D π) ≠ 0 :=
    fun h0 => hπD0 (hinjDL (by rw [h0, map_zero]))
  have hmaxL : maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap D (Localization.AtPrime P) (algebraMap O D π)} := by
    rw [hB, h𝔪D_span, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    intro hF
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmaxL, Ideal.span_singleton_eq_bot] at hF
    exact hπL0 hF
  have hprinc : (maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
    rw [hmaxL]
    exact ⟨⟨_, rfl⟩⟩
  exact ⟨((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 4).mpr hprinc, hB⟩

end ConstExtCore

namespace Algebra p2m_export "Algebra" "isIntegral_iff algebraMap adjoin_le smul_def adjoin IsSeparable.isSeparable subset_adjoin adjoin_singleton_eq_range_aeval adjoin_eq_ring_closure mem_bot adjoin_induction" namespace adjoin end Algebra.adjoin
p2m_open_scoped "Algebra Algebra.adjoin" in

theorem Algebra.adjoin.isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
    {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing M] [IsDomain M] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (e : M) (f : Polynomial O) (hf : f.Monic) (hfe : Polynomial.aeval e f = 0)
    (hsep : (f.map (IsLocalRing.residue O)).Separable)
    (P : Ideal ↥(Algebra.adjoin O ({e} : Set M))) [P.IsPrime]
    (hP : (IsLocalRing.maximalIdeal O).map (algebraMap O ↥(Algebra.adjoin O ({e} : Set M))) ≤ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        ((IsLocalRing.maximalIdeal O).map (algebraMap O ↥(Algebra.adjoin O ({e} : Set M)))).map
          (algebraMap ↥(Algebra.adjoin O ({e} : Set M)) (Localization.AtPrime P)) := by
  have hinjD : Function.Injective (algebraMap O ↥(Algebra.adjoin O ({e} : Set M))) := by
    intro a b h
    apply hinj
    have := congrArg (Subtype.val : ↥(Algebra.adjoin O ({e} : Set M)) → M) h
    simpa only [Subalgebra.coe_algebraMap] using this
  let e' : ↥(Algebra.adjoin O ({e} : Set M)) := ⟨e, Algebra.subset_adjoin (Set.mem_singleton e)⟩
  have hval : ∀ p : Polynomial O,
      ((Polynomial.aeval e' p : ↥(Algebra.adjoin O ({e} : Set M))) : M) = Polynomial.aeval e p := by
    intro p
    exact (Polynomial.aeval_algHom_apply (Algebra.adjoin O ({e} : Set M)).val e' p).symm
  have hgen : Function.Surjective (Polynomial.aeval (R := O) e') := by
    intro x
    have hx : (x : M) ∈ (Polynomial.aeval (R := O) e).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact x.2
    obtain ⟨p, hp⟩ := hx
    exact ⟨p, Subtype.ext (by rw [hval]; exact hp)⟩
  have hfe' : Polynomial.aeval e' f = 0 := Subtype.ext (by rw [hval, hfe]; rfl)
  exact ConstExtCore.isDiscreteValuationRing_localization_of_surjective_aeval hinjD e' hgen f hf hfe' hsep P hP

theorem ConstExt.local_picture
    {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field M] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (e : M) (f : Polynomial O) (hf : f.Monic) (hfe : Polynomial.aeval e f = 0)
    (hsep : (f.map (IsLocalRing.residue O)).Separable)
    (W : ValuationSubring M) (hOW : ∀ b : O, algebraMap O M b ∈ W) (heW : e ∈ W)
    (hdomW : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O → W.valuation (algebraMap O M b) < 1)
    (P : Ideal ↥(Algebra.adjoin O ({e} : Set M)))
    (hPW : ∀ d : ↥(Algebra.adjoin O ({e} : Set M)), d ∈ P ↔ W.valuation (d : M) < 1)
    (π : O) (hπ : Irreducible π) :
    (∀ y ∈ Subfield.closure (Set.range (algebraMap O M) ∪ {e}),
      y ∈ W ↔ ∃ a b : ↥(Algebra.adjoin O ({e} : Set M)), b ∉ P ∧ y = (a : M) / (b : M)) ∧
    (∀ y ∈ Subfield.closure (Set.range (algebraMap O M) ∪ {e}), W.valuation y < 1 →
      ∃ y' ∈ W, y = algebraMap O M π * y') ∧
    (∀ y ∈ Subfield.closure (Set.range (algebraMap O M) ∪ {e}), y ∈ W → y ≠ 0 →
      ∃ (n : ℕ) (u : M), u ∈ W ∧ W.valuation u = 1 ∧ y = algebraMap O M π ^ n * u) := by
  classical

  let W' : Subalgebra O M :=
    { W.toSubring with
      algebraMap_mem' := hOW }
  have hDW' : Algebra.adjoin O ({e} : Set M) ≤ W' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr heW)
  have hDW : ∀ d : ↥(Algebra.adjoin O ({e} : Set M)), (d : M) ∈ W := fun d => hDW' d.2
  have hvle : ∀ d : ↥(Algebra.adjoin O ({e} : Set M)), W.valuation (d : M) ≤ 1 :=
    fun d => (W.valuation_le_one_iff _).mpr (hDW d)
  have hv1 : ∀ d : ↥(Algebra.adjoin O ({e} : Set M)), d ∉ P ↔ W.valuation (d : M) = 1 := by
    intro d
    rw [hPW, not_lt]
    exact ⟨fun h => le_antisymm (hvle d) h, fun h => h.ge⟩
  have hne0 : ∀ d : ↥(Algebra.adjoin O ({e} : Set M)), d ∉ P → (d : M) ≠ 0 := by
    intro d hd h0
    have h1 := (hv1 d).mp hd
    rw [h0, map_zero] at h1
    exact zero_ne_one h1

  let φ : ↥(Algebra.adjoin O ({e} : Set M)) →+* ↥W :=
    { toFun := fun d => ⟨(d : M), hDW d⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hPeq : P = (IsLocalRing.maximalIdeal ↥W).comap φ := by
    ext d
    rw [Ideal.mem_comap, hPW, ValuationSubring.valuation_lt_one_iff]
    rfl
  haveI hPp : P.IsPrime := hPeq ▸ Ideal.comap_isPrime φ _
  have hP𝔪 : (IsLocalRing.maximalIdeal O).map (algebraMap O ↥(Algebra.adjoin O ({e} : Set M))) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, hPW, Subalgebra.coe_algebraMap]
    exact hdomW b hb

  obtain ⟨hDVR, hmax⟩ := Algebra.adjoin.isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
    hinj e f hf hfe hsep P hP𝔪
  haveI := hDVR
  have hπDM : ((algebraMap O ↥(Algebra.adjoin O ({e} : Set M)) π : ↥(Algebra.adjoin O ({e} : Set M))) : M) =
      algebraMap O M π := Subalgebra.coe_algebraMap _ π
  have h𝔪O : IsLocalRing.maximalIdeal O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hmaxL : IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap ↥(Algebra.adjoin O ({e} : Set M)) (Localization.AtPrime P)
        (algebraMap O ↥(Algebra.adjoin O ({e} : Set M)) π)} := by
    rw [hmax, h𝔪O, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hπL : Irreducible (algebraMap ↥(Algebra.adjoin O ({e} : Set M)) (Localization.AtPrime P)
      (algebraMap O ↥(Algebra.adjoin O ({e} : Set M)) π)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmaxL
  have hinjL : Function.Injective (algebraMap ↥(Algebra.adjoin O ({e} : Set M)) (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hcoe : ∀ {x y : ↥(Algebra.adjoin O ({e} : Set M))},
      algebraMap _ (Localization.AtPrime P) x = algebraMap _ (Localization.AtPrime P) y → (x : M) = (y : M) :=
    fun h => congrArg Subtype.val (hinjL h)

  have hDsub : (Algebra.adjoin O ({e} : Set M)).toSubring = Subring.closure (Set.range (algebraMap O M) ∪ {e}) :=
    Algebra.adjoin_eq_ring_closure _
  have hfrac : ∀ y ∈ Subfield.closure (Set.range (algebraMap O M) ∪ {e}),
      ∃ a b : ↥(Algebra.adjoin O ({e} : Set M)), (b : M) ≠ 0 ∧ y = (a : M) / (b : M) := by
    intro y hy
    rw [Subfield.mem_closure_iff] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    rw [← hDsub] at ha hb
    by_cases hb0 : b = 0
    · refine ⟨0, 1, ?_, ?_⟩
      · rw [OneMemClass.coe_one]; exact one_ne_zero
      · rw [hb0, div_zero, ZeroMemClass.coe_zero, zero_div]
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, rfl⟩

  have hin : ∀ a b : ↥(Algebra.adjoin O ({e} : Set M)), b ∉ P → (a : M) / (b : M) ∈ W := by
    intro a b hb
    rw [← W.valuation_le_one_iff, map_div₀, (hv1 b).mp hb, div_one]
    exact hvle a

  have hout : ∀ a b : ↥(Algebra.adjoin O ({e} : Set M)), (b : M) ≠ 0 → (a : M) / (b : M) ∈ W →
      ∃ a' b' : ↥(Algebra.adjoin O ({e} : Set M)), b' ∉ P ∧ (a : M) / (b : M) = (a' : M) / (b' : M) := by
    intro a b hb0 hW
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap _ (Localization.AtPrime P) a) (algebraMap _ (Localization.AtPrime P) b)
    rw [← IsLocalization.mk'_sec (M := P.primeCompl) (Localization.AtPrime P) c] at hc
    have hsP : ((IsLocalization.sec P.primeCompl c).2 : ↥(Algebra.adjoin O ({e} : Set M))) ∉ P :=
      (IsLocalization.sec P.primeCompl c).2.2
    have hs0 := hne0 _ hsP
    rcases hc with hc | hc
    ·
      have h1 : algebraMap _ (Localization.AtPrime P) (a * (IsLocalization.sec P.primeCompl c).1) =
          algebraMap _ (Localization.AtPrime P) (b * (IsLocalization.sec P.primeCompl c).2) := by
        rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
      have h2M := hcoe h1
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul] at h2M
      have ha₂0 : ((IsLocalization.sec P.primeCompl c).1 : M) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h2M
        rcases mul_eq_zero.mp h2M.symm with h | h
        · exact hb0 h
        · exact hs0 h
      have hab : (a : M) / (b : M) = ((IsLocalization.sec P.primeCompl c).2 : M) / ((IsLocalization.sec P.primeCompl c).1 : M) := by
        rw [div_eq_div_iff hb0 ha₂0]
        linear_combination h2M
      refine ⟨_, _, ?_, hab⟩
      intro ha₂P
      have hlt : W.valuation ((IsLocalization.sec P.primeCompl c).1 : M) < 1 := (hPW _).mp ha₂P
      have hW' := (W.valuation_le_one_iff _).mpr hW
      rw [hab] at hW'
      have hvs : W.valuation ((IsLocalization.sec P.primeCompl c).2 : M) =
          W.valuation (((IsLocalization.sec P.primeCompl c).2 : M) / ((IsLocalization.sec P.primeCompl c).1 : M)) *
            W.valuation ((IsLocalization.sec P.primeCompl c).1 : M) := by
        rw [← map_mul, div_mul_cancel₀ _ ha₂0]
      have : W.valuation ((IsLocalization.sec P.primeCompl c).2 : M) < 1 := by
        rw [hvs]
        calc _ ≤ 1 * W.valuation ((IsLocalization.sec P.primeCompl c).1 : M) := mul_le_mul_left hW' _
          _ < 1 := by rw [one_mul]; exact hlt
      rw [(hv1 _).mp hsP] at this
      exact lt_irrefl _ this
    ·
      have h1 : algebraMap _ (Localization.AtPrime P) (b * (IsLocalization.sec P.primeCompl c).1) =
          algebraMap _ (Localization.AtPrime P) (a * (IsLocalization.sec P.primeCompl c).2) := by
        rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
      have h2M := hcoe h1
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul] at h2M
      have hab : (a : M) / (b : M) = ((IsLocalization.sec P.primeCompl c).1 : M) / ((IsLocalization.sec P.primeCompl c).2 : M) := by
        rw [div_eq_div_iff hb0 hs0]
        linear_combination h2M.symm
      exact ⟨_, _, hsP, hab⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨a, b, hb0, rfl⟩ := hfrac y hy
    constructor
    · intro hW
      obtain ⟨a', b', hb', heq⟩ := hout a b hb0 hW
      exact ⟨a', b', hb', heq⟩
    · rintro ⟨a', b', hb', heq⟩
      rw [heq]
      exact hin a' b' hb'
  ·
    intro y hy hlt
    have hW : y ∈ W := (W.valuation_le_one_iff _).mp hlt.le
    obtain ⟨a, b, hb0, rfl⟩ := hfrac y hy
    obtain ⟨a', b', hb', heq⟩ := hout a b hb0 hW
    have hb'0 := hne0 b' hb'
    have ha' : a' ∈ P := by
      rw [hPW]
      have h := hlt
      rw [heq, map_div₀, (hv1 b').mp hb', div_one] at h
      exact h
    have hmem : algebraMap _ (Localization.AtPrime P) a' ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P a').mpr ha'
    rw [hmaxL, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [← IsLocalization.mk'_sec (M := P.primeCompl) (Localization.AtPrime P) c] at hc
    have hs₂P : ((IsLocalization.sec P.primeCompl c).2 : ↥(Algebra.adjoin O ({e} : Set M))) ∉ P :=
      (IsLocalization.sec P.primeCompl c).2.2
    have hs₂0 := hne0 _ hs₂P
    have h1 : algebraMap _ (Localization.AtPrime P) (a' * (IsLocalization.sec P.primeCompl c).2) =
        algebraMap _ (Localization.AtPrime P)
          (algebraMap O ↥(Algebra.adjoin O ({e} : Set M)) π * (IsLocalization.sec P.primeCompl c).1) := by
      rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]
    have h2M := hcoe h1
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hπDM] at h2M
    refine ⟨((IsLocalization.sec P.primeCompl c).1 : M) / ((b' * (IsLocalization.sec P.primeCompl c).2 :
        ↥(Algebra.adjoin O ({e} : Set M))) : M), hin _ _ (fun h => (hPp.mem_or_mem h).elim hb' hs₂P), ?_⟩
    rw [heq, Subalgebra.coe_mul, mul_div_assoc', div_eq_div_iff hb'0 (mul_ne_zero hb'0 hs₂0)]
    linear_combination (b' : M) * h2M
  ·
    intro y hy hW hy0
    obtain ⟨a, b, hb0, rfl⟩ := hfrac y hy
    obtain ⟨a', b', hb', heq⟩ := hout a b hb0 hW
    have hb'0 := hne0 b' hb'
    have ha'0 : (a' : M) ≠ 0 := by
      intro h0
      apply hy0
      rw [heq, h0, zero_div]
    have ha'L0 : algebraMap _ (Localization.AtPrime P) a' ≠ 0 := by
      intro h
      exact ha'0 (by rw [hcoe (h.trans (map_zero _).symm), ZeroMemClass.coe_zero])
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha'L0 hπL
    set a₃ : ↥(Algebra.adjoin O ({e} : Set M)) := (IsLocalization.sec P.primeCompl (u : Localization.AtPrime P)).1 with ha₃
    set s₃ : P.primeCompl := (IsLocalization.sec P.primeCompl (u : Localization.AtPrime P)).2 with hs₃
    have hu' : IsLocalization.mk' (Localization.AtPrime P) a₃ s₃ = (u : Localization.AtPrime P) :=
      IsLocalization.mk'_sec (M := P.primeCompl) (Localization.AtPrime P) (u : Localization.AtPrime P)
    have hs₃P : ((s₃ : ↥(Algebra.adjoin O ({e} : Set M)))) ∉ P := s₃.2
    have hs₃0 := hne0 _ hs₃P
    have ha₃P : a₃ ∉ P := by
      have h := u.isUnit
      rw [← hu', IsLocalization.AtPrime.isUnit_mk'_iff] at h
      exact h
    have h1 : algebraMap _ (Localization.AtPrime P) (a' * (s₃ : ↥(Algebra.adjoin O ({e} : Set M)))) =
        algebraMap _ (Localization.AtPrime P) (a₃ * algebraMap O ↥(Algebra.adjoin O ({e} : Set M)) π ^ n) := by
      rw [map_mul, map_mul, map_pow, hu, ← hu', mul_right_comm, IsLocalization.mk'_spec]
    have h2M := hcoe h1
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, hπDM] at h2M
    refine ⟨n, (a₃ : M) / ((b' * (s₃ : ↥(Algebra.adjoin O ({e} : Set M))) : ↥(Algebra.adjoin O ({e} : Set M))) : M),
      hin _ _ (fun h => (hPp.mem_or_mem h).elim hb' hs₃P), ?_, ?_⟩
    · rw [map_div₀, Subalgebra.coe_mul, map_mul, (hv1 _).mp ha₃P, (hv1 _).mp hb', (hv1 _).mp hs₃P, mul_one, div_one]
    · rw [heq, Subalgebra.coe_mul, mul_div_assoc', div_eq_div_iff hb'0 (mul_ne_zero hb'0 hs₃0)]
      linear_combination (b' : M) * h2M

namespace ConstExt

theorem exists_finset_of_mem_closure {M : Type*} [Field M] (S T : Set M) {x : M}
    (hx : x ∈ Subfield.closure (S ∪ T)) : ∃ T₀ : Finset M, (↑T₀ : Set M) ⊆ T ∧ x ∈ Subfield.closure (S ∪ ↑T₀) := by
  classical
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨∅, by simp, Subfield.subset_closure (Or.inl hy)⟩
    · exact ⟨{y}, by simpa using hy, Subfield.subset_closure (Or.inr (by simp))⟩
  | one => exact ⟨∅, by simp, one_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨T₁, h1, hy⟩ := hy
    obtain ⟨T₂, h2, hz⟩ := hz
    refine ⟨T₁ ∪ T₂, by simpa using And.intro h1 h2, add_mem ?_ ?_⟩
    · exact Subfield.closure_mono (Set.union_subset_union_right _ (by simp)) hy
    · exact Subfield.closure_mono (Set.union_subset_union_right _ (by simp)) hz
  | neg y _ hy =>
    obtain ⟨T₁, h1, hy⟩ := hy
    exact ⟨T₁, h1, neg_mem hy⟩
  | inv y _ hy =>
    obtain ⟨T₁, h1, hy⟩ := hy
    exact ⟨T₁, h1, inv_mem hy⟩
  | mul y z _ _ hy hz =>
    obtain ⟨T₁, h1, hy⟩ := hy
    obtain ⟨T₂, h2, hz⟩ := hz
    refine ⟨T₁ ∪ T₂, by simpa using And.intro h1 h2, mul_mem ?_ ?_⟩
    · exact Subfield.closure_mono (Set.union_subset_union_right _ (by simp)) hy
    · exact Subfield.closure_mono (Set.union_subset_union_right _ (by simp)) hz

section Setting

variable {K M O : Type*} [Field K] [Field M] [Algebra K M]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]
  (hinj : Function.Injective (algebraMap O M))
  (hKO : ∀ c : K, algebraMap K M c ∈ (algebraMap O M).range)

noncomputable def secK : K →+* O where
  toFun c := (hKO c).choose
  map_one' := hinj (by rw [(hKO 1).choose_spec, map_one, map_one])
  map_mul' a b := hinj (by rw [(hKO (a * b)).choose_spec, map_mul, map_mul, (hKO a).choose_spec, (hKO b).choose_spec])
  map_zero' := hinj (by rw [(hKO 0).choose_spec, map_zero, map_zero])
  map_add' a b := hinj (by rw [(hKO (a + b)).choose_spec, map_add, map_add, (hKO a).choose_spec, (hKO b).choose_spec])

theorem algebraMap_secK (c : K) : algebraMap O M (secK hinj hKO c) = algebraMap K M c :=
  (hKO c).choose_spec

theorem algebraMap_comp_secK : (algebraMap O M).comp (secK hinj hKO) = algebraMap K M :=
  RingHom.ext (algebraMap_secK hinj hKO)

include hinj hKO in

theorem exists_monic_aeval_eq_zero_separable {e : M} (he : IsSeparable K e) :
    ∃ f : Polynomial O, f.Monic ∧ Polynomial.aeval e f = 0 ∧ (f.map (IsLocalRing.residue O)).Separable := by
  refine ⟨(minpoly K e).map (secK hinj hKO), (minpoly.monic he.isIntegral).map _, ?_, ?_⟩
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_secK, ← Polynomial.aeval_def, minpoly.aeval]
  · rw [Polynomial.map_map]
    exact Polynomial.Separable.map he

end Setting

section Constants

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

theorem mem_of_isIntegral (W : ValuationSubring M) (hKW : ∀ c : K, algebraMap K M c ∈ W)
    {x : M} (hx : IsIntegral K x) : x ∈ W := by
  obtain ⟨p, hp, hpx⟩ := hx
  let φ : K →+* ↥W := (algebraMap K M).codRestrict W.toSubring hKW
  have hcomp : (algebraMap ↥W M).comp φ = algebraMap K M := RingHom.ext fun _ => rfl
  have hint : IsIntegral ↥W x := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hpx
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W) (K := M)).mp hint
  rw [← hy]
  exact y.2

theorem isSeparable_of_mem_adjoin (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    {x : M} (hx : x ∈ IntermediateField.adjoin K (E : Set M)) : IsSeparable K x := by
  haveI : Algebra.IsSeparable K ↥(IntermediateField.adjoin K (E : Set M)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K M).mpr hE
  have h := Algebra.IsSeparable.isSeparable K (⟨x, hx⟩ : ↥(IntermediateField.adjoin K (E : Set M)))
  unfold IsSeparable at h ⊢
  rwa [show x = algebraMap ↥(IntermediateField.adjoin K (E : Set M)) M ⟨x, hx⟩ from rfl,
    minpoly.algebraMap_eq (algebraMap ↥(IntermediateField.adjoin K (E : Set M)) M).injective]

end Constants

section Primitive

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

theorem exists_primitive (S : Set M) (hKS : Set.range (algebraMap K M) ⊆ S) (T₀ : Finset M)
    (hT : ∀ t ∈ T₀, IsSeparable K t) :
    ∃ e : M, e ∈ IntermediateField.adjoin K (↑T₀ : Set M) ∧
      Subfield.closure (S ∪ ↑T₀) ≤ Subfield.closure (S ∪ {e}) := by
  classical
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K (↑T₀ : Set M)) :=
    IntermediateField.finiteDimensional_adjoin fun t ht => (hT t ht).isIntegral
  haveI : Algebra.IsSeparable K ↥(IntermediateField.adjoin K (↑T₀ : Set M)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K M).mpr hT
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K ↥(IntermediateField.adjoin K (↑T₀ : Set M))
  refine ⟨(α : M), α.2, Subfield.closure_le.mpr ?_⟩
  rintro t (ht | ht)
  · exact Subfield.subset_closure (Or.inl ht)
  · have htF : t ∈ IntermediateField.adjoin K (↑T₀ : Set M) := IntermediateField.subset_adjoin K _ ht

    have h1 : (IntermediateField.adjoin K ({α} : Set ↥(IntermediateField.adjoin K (↑T₀ : Set M)))).map
        (IntermediateField.adjoin K (↑T₀ : Set M)).val = IntermediateField.adjoin K ({(α : M)} : Set M) := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
      rfl
    have h2 : t ∈ IntermediateField.adjoin K ({(α : M)} : Set M) := by
      rw [← h1, hα]
      exact ⟨⟨t, htF⟩, trivial, rfl⟩
    exact Subfield.closure_mono (Set.union_subset_union hKS le_rfl) h2

end Primitive

section Assembly

variable {K M O : Type*} [Field K] [Field M] [Algebra K M]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]

theorem adjoin_le_valuationSubring (e : M) (W : ValuationSubring M) (hOW : ∀ b : O, algebraMap O M b ∈ W)
    (heW : e ∈ W) : ∀ d ∈ Algebra.adjoin O ({e} : Set M), d ∈ W := by
  intro d hd
  induction hd using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff] at hx; rw [hx]; exact heW
  | algebraMap r => exact hOW r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem valuation_eq_one_of_mem_adjoin (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (W : ValuationSubring M) (hKW : ∀ c : K, algebraMap K M c ∈ W)
    {c : M} (hc : c ∈ IntermediateField.adjoin K (E : Set M)) (hc0 : c ≠ 0) : W.valuation c = 1 := by
  have hmem : ∀ x ∈ IntermediateField.adjoin K (E : Set M), x ∈ W :=
    fun x hx => mem_of_isIntegral W hKW (isSeparable_of_mem_adjoin E hE hx).isIntegral
  apply le_antisymm ((W.valuation_le_one_iff _).mpr (hmem c hc))
  have h1 : W.valuation c⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr (hmem _ (inv_mem hc))
  have hc0' : W.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hc0')] at h1
  exact h1

theorem valuation_lt_one_iff_of_mem_adjoin (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (W W' : ValuationSubring M) (hKW : ∀ c : K, algebraMap K M c ∈ W) (hKW' : ∀ c : K, algebraMap K M c ∈ W')
    (hOW : ∀ b : O, algebraMap O M b ∈ W) (hOW' : ∀ b : O, algebraMap O M b ∈ W')
    (hval : ∀ b : O, ∃ c : M, c ∈ E ∧
      W.valuation (algebraMap O M b - c) < 1 ∧ W'.valuation (algebraMap O M b - c) < 1)
    {e : M} (he : e ∈ IntermediateField.adjoin K (E : Set M))
    {d : M} (hd : d ∈ Algebra.adjoin O ({e} : Set M)) :
    W.valuation d < 1 ↔ W'.valuation d < 1 := by
  have hmemW : ∀ x ∈ IntermediateField.adjoin K (E : Set M), x ∈ W :=
    fun x hx => mem_of_isIntegral W hKW (isSeparable_of_mem_adjoin E hE hx).isIntegral
  have hmemW' : ∀ x ∈ IntermediateField.adjoin K (E : Set M), x ∈ W' :=
    fun x hx => mem_of_isIntegral W' hKW' (isSeparable_of_mem_adjoin E hE hx).isIntegral
  have heW : e ∈ W := hmemW e he
  have heW' : e ∈ W' := hmemW' e he

  have key : ∀ d ∈ Algebra.adjoin O ({e} : Set M), ∃ c ∈ IntermediateField.adjoin K (E : Set M),
      W.valuation (d - c) < 1 ∧ W'.valuation (d - c) < 1 := by
    intro d hd
    induction hd using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      refine ⟨x, hx ▸ he, ?_, ?_⟩ <;> simp
    | algebraMap r =>
      obtain ⟨c, hc, h1, h2⟩ := hval r
      exact ⟨c, IntermediateField.subset_adjoin K _ hc, h1, h2⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨c, hc, h1, h2⟩ := ihx
      obtain ⟨c', hc', h1', h2'⟩ := ihy
      refine ⟨c + c', add_mem hc hc', ?_, ?_⟩
      · rw [show x + y - (c + c') = (x - c) + (y - c') by ring]; exact Valuation.map_add_lt _ h1 h1'
      · rw [show x + y - (c + c') = (x - c) + (y - c') by ring]; exact Valuation.map_add_lt _ h2 h2'
    | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc, h1, h2⟩ := ihx
      obtain ⟨c', hc', h1', h2'⟩ := ihy
      refine ⟨c * c', mul_mem hc hc', ?_, ?_⟩
      · rw [show x * y - c * c' = (x - c) * y + c * (y - c') by ring]
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [map_mul]
          calc W.valuation (x - c) * W.valuation y ≤ W.valuation (x - c) * 1 :=
                mul_le_mul_right ((W.valuation_le_one_iff _).mpr (adjoin_le_valuationSubring e W hOW heW y hy)) _
            _ < 1 := by rw [mul_one]; exact h1
        · rw [map_mul]
          calc W.valuation c * W.valuation (y - c') ≤ 1 * W.valuation (y - c') :=
                mul_le_mul_left ((W.valuation_le_one_iff _).mpr (hmemW c hc)) _
            _ < 1 := by rw [one_mul]; exact h1'
      · rw [show x * y - c * c' = (x - c) * y + c * (y - c') by ring]
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [map_mul]
          calc W'.valuation (x - c) * W'.valuation y ≤ W'.valuation (x - c) * 1 :=
                mul_le_mul_right ((W'.valuation_le_one_iff _).mpr (adjoin_le_valuationSubring e W' hOW' heW' y hy)) _
            _ < 1 := by rw [mul_one]; exact h2
        · rw [map_mul]
          calc W'.valuation c * W'.valuation (y - c') ≤ 1 * W'.valuation (y - c') :=
                mul_le_mul_left ((W'.valuation_le_one_iff _).mpr (hmemW' c hc)) _
            _ < 1 := by rw [one_mul]; exact h2'
  obtain ⟨c, hc, h1, h2⟩ := key d hd
  have one_dir : ∀ (W W' : ValuationSubring M), (∀ c : K, algebraMap K M c ∈ W) → W.valuation (d - c) < 1 →
      W'.valuation (d - c) < 1 → W.valuation d < 1 → W'.valuation d < 1 := by
    intro W W' hKW hW hW' hd1
    have hc1 : W.valuation c < 1 := by
      have : c = d + -(d - c) := by ring
      rw [this]
      exact Valuation.map_add_lt _ hd1 (by rwa [Valuation.map_neg])
    have hc0 : c = 0 := by
      by_contra hc0
      exact absurd (valuation_eq_one_of_mem_adjoin E hE W hKW hc hc0) (ne_of_lt hc1)
    rw [hc0, sub_zero] at hW'
    exact hW'
  exact ⟨one_dir W W' hKW h1 h2, one_dir W' W hKW' h2 h1⟩

end Assembly

section Main

variable {K M O : Type*} [Field K] [Field M] [Algebra K M]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]

theorem exists_centre (e : M) (W : ValuationSubring M) (hOW : ∀ b : O, algebraMap O M b ∈ W) (heW : e ∈ W) :
    ∃ P : Ideal ↥(Algebra.adjoin O ({e} : Set M)),
      ∀ d : ↥(Algebra.adjoin O ({e} : Set M)), d ∈ P ↔ W.valuation (d : M) < 1 := by
  let ι : ↥(Algebra.adjoin O ({e} : Set M)) →+* ↥W :=
    (Algebra.adjoin O ({e} : Set M)).val.toRingHom.codRestrict W.toSubring
      (fun d => adjoin_le_valuationSubring e W hOW heW d d.2)
  refine ⟨(IsLocalRing.maximalIdeal ↥W).comap ι, fun d => ?_⟩
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem le_of_forall_exists_sub_valuation_lt_one
    (hinj : Function.Injective (algebraMap O M))
    (hKO : ∀ c : K, algebraMap K M c ∈ (algebraMap O M).range)
    (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (hgen : Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) = ⊤)
    (W W' : ValuationSubring M) (hOW : ∀ b : O, algebraMap O M b ∈ W) (hOW' : ∀ b : O, algebraMap O M b ∈ W')
    (hdom : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O →
      W.valuation (algebraMap O M b) < 1 ∧ W'.valuation (algebraMap O M b) < 1)
    (hval : ∀ b : O, ∃ c : M, c ∈ E ∧
      W.valuation (algebraMap O M b - c) < 1 ∧ W'.valuation (algebraMap O M b - c) < 1) :
    W ≤ W' := by
  classical
  intro x hxW
  have hKW : ∀ c : K, algebraMap K M c ∈ W := fun c => by
    obtain ⟨b, hb⟩ := hKO c; rw [← hb]; exact hOW b
  have hKW' : ∀ c : K, algebraMap K M c ∈ W' := fun c => by
    obtain ⟨b, hb⟩ := hKO c; rw [← hb]; exact hOW' b
  have hKS : Set.range (algebraMap K M) ⊆ ((algebraMap O M).range : Set M) := by
    rintro _ ⟨c, rfl⟩; exact hKO c

  have hx : x ∈ Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) := by rw [hgen]; trivial
  obtain ⟨T₀, hT₀E, hxT⟩ := exists_finset_of_mem_closure _ _ hx
  have hTsep : ∀ t ∈ T₀, IsSeparable K t := fun t ht => hE t (hT₀E ht)
  obtain ⟨e, heT, hle⟩ := exists_primitive (K := K) _ hKS T₀ hTsep
  have heE : e ∈ IntermediateField.adjoin K (E : Set M) := IntermediateField.adjoin.mono K _ _ hT₀E heT
  have hesep : IsSeparable K e := isSeparable_of_mem_adjoin E hE heE
  have hxe : x ∈ Subfield.closure (Set.range (algebraMap O M) ∪ {e}) := by
    have := hle hxT
    rwa [RingHom.coe_range] at this
  obtain ⟨f, hf, hfe, hsep⟩ := exists_monic_aeval_eq_zero_separable hinj hKO hesep
  have heW : e ∈ W := mem_of_isIntegral W hKW hesep.isIntegral
  have heW' : e ∈ W' := mem_of_isIntegral W' hKW' hesep.isIntegral

  obtain ⟨P, hPW⟩ := exists_centre e W hOW heW
  have hPW' : ∀ d : ↥(Algebra.adjoin O ({e} : Set M)), d ∈ P ↔ W'.valuation (d : M) < 1 := fun d =>
    (hPW d).trans (valuation_lt_one_iff_of_mem_adjoin E hE W W' hKW hKW' hOW hOW' hval heE d.2)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨h1, -, -⟩ := local_picture hinj e f hf hfe hsep W hOW heW (fun b hb => (hdom b hb).1) P hPW π hπ
  obtain ⟨h1', -, -⟩ := local_picture hinj e f hf hfe hsep W' hOW' heW' (fun b hb => (hdom b hb).2) P hPW' π hπ
  exact (h1' x hxe).mpr ((h1 x hxe).mp hxW)

end Main

end ConstExt

theorem ConstExt.valuationSubring_eq_of_forall_exists_sub_valuation_lt_one
    {K M O : Type*} [Field K] [Field M] [Algebra K M]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (hKO : ∀ c : K, algebraMap K M c ∈ (algebraMap O M).range)
    (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (hgen : Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) = ⊤)
    (V V' : ValuationSubring M) (hOV : ∀ b : O, algebraMap O M b ∈ V) (hOV' : ∀ b : O, algebraMap O M b ∈ V')
    (hdom : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O →
      V.valuation (algebraMap O M b) < 1 ∧ V'.valuation (algebraMap O M b) < 1)
    (hval : ∀ b : O, ∃ c : M, c ∈ E ∧
      V.valuation (algebraMap O M b - c) < 1 ∧ V'.valuation (algebraMap O M b - c) < 1) :
    V = V' :=
  le_antisymm
    (ConstExt.le_of_forall_exists_sub_valuation_lt_one hinj hKO E hE hgen V V' hOV hOV' hdom hval)
    (ConstExt.le_of_forall_exists_sub_valuation_lt_one hinj hKO E hE hgen V' V hOV' hOV
      (fun b hb => (hdom b hb).symm) (fun b => by obtain ⟨c, hc, h1, h2⟩ := hval b; exact ⟨c, hc, h2, h1⟩))

theorem ConstExt.isPrincipalIdealRing_and_ne_top_and_maximalIdeal_eq_span
    {K M O : Type*} [Field K] [Field M] [Algebra K M]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (hKO : ∀ c : K, algebraMap K M c ∈ (algebraMap O M).range)
    (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (hgen : Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) = ⊤)
    (V : ValuationSubring M) (hOV : ∀ b : O, algebraMap O M b ∈ V)
    (hdom : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O → V.valuation (algebraMap O M b) < 1)
    (π : O) (hπ : Irreducible π) :
    IsPrincipalIdealRing ↥V ∧ V ≠ ⊤ ∧
      IsLocalRing.maximalIdeal ↥V = Ideal.span {(⟨algebraMap O M π, hOV π⟩ : ↥V)} := by
  classical
  have hKV : ∀ c : K, algebraMap K M c ∈ V := fun c => by
    obtain ⟨b, hb⟩ := hKO c; rw [← hb]; exact hOV b
  have hKS : Set.range (algebraMap K M) ⊆ ((algebraMap O M).range : Set M) := by
    rintro _ ⟨c, rfl⟩; exact hKO c
  have hπm : π ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal]; exact hπ.not_isUnit
  have hπV : V.valuation (algebraMap O M π) < 1 := hdom π hπm
  have hπ0 : algebraMap O M π ≠ 0 := fun h0 => hπ.ne_zero (hinj (by rw [h0, map_zero]))

  have hloc : ∀ x : M, ∃ (e : M) (f : Polynomial O), f.Monic ∧ Polynomial.aeval e f = 0 ∧
      (f.map (IsLocalRing.residue O)).Separable ∧ e ∈ V ∧
      x ∈ Subfield.closure (Set.range (algebraMap O M) ∪ {e}) := by
    intro x
    have hx : x ∈ Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) := by rw [hgen]; trivial
    obtain ⟨T₀, hT₀E, hxT⟩ := ConstExt.exists_finset_of_mem_closure _ _ hx
    have hTsep : ∀ t ∈ T₀, IsSeparable K t := fun t ht => hE t (hT₀E ht)
    obtain ⟨e, heT, hle⟩ := ConstExt.exists_primitive (K := K) _ hKS T₀ hTsep
    have heE : e ∈ IntermediateField.adjoin K (E : Set M) := IntermediateField.adjoin.mono K _ _ hT₀E heT
    have hesep : IsSeparable K e := ConstExt.isSeparable_of_mem_adjoin E hE heE
    obtain ⟨f, hf, hfe, hsep⟩ := ConstExt.exists_monic_aeval_eq_zero_separable hinj hKO hesep
    refine ⟨e, f, hf, hfe, hsep, ConstExt.mem_of_isIntegral V hKV hesep.isIntegral, ?_⟩
    have := hle hxT
    rwa [RingHom.coe_range] at this

  have hne : V ≠ ⊤ := by
    intro h
    have : algebraMap O M π ∈ V := hOV π
    have hu : V.valuation (algebraMap O M π) = 1 := by
      have hinv : (algebraMap O M π)⁻¹ ∈ V := by rw [h]; trivial
      apply le_antisymm ((V.valuation_le_one_iff _).mpr this)
      have h1 : V.valuation (algebraMap O M π)⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr hinv
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hπ0))] at h1
      exact h1
    rw [hu] at hπV
    exact lt_irrefl _ hπV

  have hmax : IsLocalRing.maximalIdeal ↥V = Ideal.span {(⟨algebraMap O M π, hOV π⟩ : ↥V)} := by
    apply le_antisymm
    · intro y hy
      rw [ValuationSubring.valuation_lt_one_iff] at hy
      obtain ⟨e, f, hf, hfe, hsep, heV, hye⟩ := hloc (y : M)
      obtain ⟨P, hPV⟩ := ConstExt.exists_centre e V hOV heV
      obtain ⟨-, h2, -⟩ := ConstExt.local_picture hinj e f hf hfe hsep V hOV heV hdom P hPV π hπ
      obtain ⟨y', hy', hyy⟩ := h2 (y : M) hye hy
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨y', hy'⟩, Subtype.ext ?_⟩
      show y' * algebraMap O M π = (y : M)
      rw [hyy, mul_comm]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (ValuationSubring.valuation_lt_one_iff _ _).mpr hπV

  have hfac : ∀ y : ↥V, y ≠ 0 → ∃ (n : ℕ) (u : (↥V)ˣ), y = (u : ↥V) * (⟨algebraMap O M π, hOV π⟩ : ↥V) ^ n := by
    intro y hy0
    obtain ⟨e, f, hf, hfe, hsep, heV, hye⟩ := hloc (y : M)
    obtain ⟨P, hPV⟩ := ConstExt.exists_centre e V hOV heV
    obtain ⟨-, -, h3⟩ := ConstExt.local_picture hinj e f hf hfe hsep V hOV heV hdom P hPV π hπ
    obtain ⟨n, u, huV, hu1, hyu⟩ := h3 (y : M) hye y.2 (fun h0 => hy0 (Subtype.ext h0))
    have hu : IsUnit (⟨u, huV⟩ : ↥V) := (ValuationSubring.valuation_eq_one_iff _ _).mpr hu1
    refine ⟨n, hu.unit, Subtype.ext ?_⟩
    show (y : M) = u * algebraMap O M π ^ n
    rw [hyu, mul_comm]
  have hirr : Irreducible (⟨algebraMap O M π, hOV π⟩ : ↥V) := by
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · have := (ValuationSubring.valuation_eq_one_iff _ _).mp hu
      exact absurd this (ne_of_lt hπV)
    · have ha0 : a ≠ 0 := fun h => hπ0 (by have := congrArg Subtype.val hab; rw [h, zero_mul] at this; exact this)
      have hb0 : b ≠ 0 := fun h => hπ0 (by have := congrArg Subtype.val hab; rw [h, mul_zero] at this; exact this)
      obtain ⟨i, ua, ha⟩ := hfac a ha0
      obtain ⟨j, ub, hb⟩ := hfac b hb0
      rcases Nat.eq_zero_or_pos i with hi | hi
      · left; rw [ha, hi, pow_zero, mul_one]; exact ua.isUnit
      rcases Nat.eq_zero_or_pos j with hj | hj
      · right; rw [hb, hj, pow_zero, mul_one]; exact ub.isUnit

      exfalso
      set p : ↥V := ⟨algebraMap O M π, hOV π⟩ with hp
      have hp0 : p ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
      have key : p * 1 = p * (((ua : ↥V) * (ub : ↥V)) * p ^ (i + j - 1)) := by
        rw [mul_one]
        conv_lhs => rw [hab, ha, hb]
        have : i + j - 1 + 1 = i + j := by omega
        rw [show p ^ i = p ^ i from rfl]
        calc (ua : ↥V) * p ^ i * ((ub : ↥V) * p ^ j) = (ua : ↥V) * (ub : ↥V) * p ^ (i + j) := by ring
          _ = (ua : ↥V) * (ub : ↥V) * (p ^ (i + j - 1) * p) := by rw [← pow_succ, this]
          _ = p * ((ua : ↥V) * (ub : ↥V) * p ^ (i + j - 1)) := by ring
      have key2 := mul_left_cancel₀ hp0 key
      have hunit : IsUnit (p ^ (i + j - 1)) := isUnit_of_mul_isUnit_right (key2 ▸ isUnit_one)
      have : 1 ≤ i + j - 1 := by omega
      have hpunit : IsUnit p := isUnit_of_dvd_unit (dvd_pow_self p (by omega)) hunit
      exact (ne_of_lt hπV) ((ValuationSubring.valuation_eq_one_iff _ _).mp hpunit)
  haveI : IsDiscreteValuationRing ↥V :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨_, hirr, fun {y} hy0 => by
        obtain ⟨n, u, hyu⟩ := hfac y hy0
        exact ⟨n, ⟨u, by rw [hyu, mul_comm]⟩⟩⟩
  exact ⟨inferInstance, hne, hmax⟩

theorem solution
    {K M O : Type*} [Field K] [Field M] [Algebra K M]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (hKO : ∀ c : K, algebraMap K M c ∈ (algebraMap O M).range)
    (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (hgen : Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) = ⊤)
    (V : ValuationSubring M) (hOV : ∀ b : O, algebraMap O M b ∈ V)
    (hdom : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O → V.valuation (algebraMap O M b) < 1)
    (π : O) (hπ : Irreducible π) :
    IsPrincipalIdealRing ↥V ∧ V ≠ ⊤ ∧
      IsLocalRing.maximalIdeal ↥V = Ideal.span {(⟨algebraMap O M π, hOV π⟩ : ↥V)} :=
  ConstExt.isPrincipalIdealRing_and_ne_top_and_maximalIdeal_eq_span hinj hKO E hE hgen V hOV hdom π hπ

end S_ValuationSubring_isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible
end P2MW
export P2MW.S_ValuationSubring_isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible (solution)
