-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.comp_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:03.11487+00:00
-- url     : https://prove2.me/submissions/28f9d1c8-20f7-46e2-99ca-37480341f7bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private theorem op_isFractionRing' (D N : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    letI := (OpToKT D N la).toAlgebra
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := (OpToKT D N la).toAlgebra
  have hinjT : Function.Injective (OTtoKT K D N) := by
    unfold OTtoKT
    exact MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
  have hinj : Function.Injective (algebraMap (Op D N la) (KTf K D N)) := by
    show Function.Injective (OpToKT D N la)
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (laT D N la).primeCompl x
    unfold OpToKT at hx
    rw [IsLocalization.lift_mk'_spec, mul_zero, RingHom.comp_apply] at hx
    have h2 : OTtoKT K D N a = 0 :=
      (injective_iff_map_eq_zero _).mp (IsFractionRing.injective (KTp K D N) (KTf K D N)) _ hx
    have h3 : a = 0 := (injective_iff_map_eq_zero _).mp hinjT _ h2
    subst h3
    exact IsLocalization.mk'_zero _
  have hC : ∀ s : 𝓞 K, OTtoKT K D N (MvPolynomial.C s) = MvPolynomial.C (algebraMap (𝓞 K) K s) :=
    fun s => MvPolynomial.map_C _ _
  have hX : ∀ i, OTtoKT K D N (MvPolynomial.X i) = MvPolynomial.X i :=
    fun i => MvPolynomial.map_X _ _
  have hcl : ∀ p : KTp K D N, ∃ s : 𝓞 K, s ≠ 0 ∧ ∃ p' : OT K D N,
      OTtoKT K D N p' = MvPolynomial.C (algebraMap (𝓞 K) K s) * p := by
    intro p
    induction p using MvPolynomial.induction_on
    next a =>
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have hy' : algebraMap (𝓞 K) K y ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
      refine ⟨y, nonZeroDivisors.ne_zero hy, MvPolynomial.C x, ?_⟩
      rw [hC, ← MvPolynomial.C_mul]
      congr 1
      first
        | (field_simp; done)
        | (rw [mul_div_assoc', mul_div_cancel_left₀ _ hy'])
        | (field_simp; ring)
    next p q hp hq =>
      obtain ⟨s1, hs1, p1, hp1⟩ := hp
      obtain ⟨s2, hs2, q1, hq1⟩ := hq
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, MvPolynomial.C s2 * p1 + MvPolynomial.C s1 * q1, ?_⟩
      rw [map_add, map_mul, map_mul, hp1, hq1, hC, hC, map_mul (algebraMap (𝓞 K) K),
        MvPolynomial.C_mul]
      ring
    next p i hp =>
      obtain ⟨s, hs, p1, hp1⟩ := hp
      exact ⟨s, hs, p1 * MvPolynomial.X i, by rw [map_mul, hp1, hX, mul_assoc]⟩
  have hCne : ∀ s : 𝓞 K, s ≠ 0 → algebraMap (KTp K D N) (KTf K D N)
      (MvPolynomial.C (algebraMap (𝓞 K) K s)) ≠ 0 := by
    intro s hs
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs
  have hOp : ∀ a : OT K D N, algebraMap (Op D N la) (KTf K D N) (algebraMap (OT K D N) (Op D N la) a) =
      algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N a) := by
    intro a
    show OpToKT D N la _ = _
    unfold OpToKT
    exact IsLocalization.lift_eq _ _
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hy))
  · intro z
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := KTp K D N) z
    obtain ⟨sp, hsp, p', hp'⟩ := hcl p
    obtain ⟨sq, hsq, q', hq'⟩ := hcl q
    have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    have e1 : algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq)) =
        algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sp)) *
          algebraMap (KTp K D N) (KTf K D N) p *
          algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sq)) := by
      rw [hOp, map_mul, hp', hC, map_mul, map_mul]
    have e2 : algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) =
        algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sq)) *
          algebraMap (KTp K D N) (KTf K D N) q *
          algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sp)) := by
      rw [hOp, map_mul, hq', hC, map_mul, map_mul]
    have hx2 : algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mp (by
        rw [e2]
        exact mul_ne_zero (mul_ne_zero (hCne sq hsq) hq0) (hCne sp hsp))
    refine ⟨⟨algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq),
      ⟨_, mem_nonZeroDivisors_of_ne_zero hx2⟩⟩, ?_⟩
    show _ * algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) = _
    rw [e1, e2]
    have h1 := hCne sq hsq
    have h2 := hCne sp hsp
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [div_mul_eq_mul_div, div_eq_iff hq0]; ring)
  · intro x y hxy
    exact ⟨1, by rw [hinj hxy]⟩
private theorem isDedekindDomain_Op (D N : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    IsDedekindDomain (Op D N la) := by
  classical
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 := by
    have hlt : la.asIdeal ^ 2 < la.asIdeal ^ 1 :=
      Ideal.pow_right_strictAnti la.asIdeal la.ne_bot la.isPrime.ne_top (by norm_num)
    rw [pow_one] at hlt
    exact SetLike.exists_of_lt hlt
  have hdvd : la.asIdeal ∣ Ideal.span {ϖ} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖ)
  obtain ⟨J, hJ⟩ := hdvd
  have hJla : ¬ J ≤ la.asIdeal := by
    intro hle
    apply hϖ2
    have hsub : Ideal.span {ϖ} ≤ la.asIdeal ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact hsub (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsJ, hsla⟩ := Set.not_subset.mp hJla
  have key : ∀ a ∈ la.asIdeal, ∃ b, s * a = ϖ * b := by
    intro a ha
    have hmem : s * a ∈ Ideal.span {ϖ} := by
      rw [hJ, mul_comm s a]
      exact Ideal.mul_mem_mul ha hsJ
    exact Ideal.mem_span_singleton.mp hmem
  have hsnot : MvPolynomial.C s ∉ laT D N la := by
    unfold laT
    rw [MvPolynomial.mem_map_C_iff]
    intro h
    apply hsla
    simpa using h 0
  have hsu : IsUnit (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s)) :=
    IsLocalization.map_units (Op D N la) (⟨MvPolynomial.C s, hsnot⟩ : (laT D N la).primeCompl)
  have hsub : ∀ a ∈ la.asIdeal, algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) ∈
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)} := by
    intro a ha
    obtain ⟨b, hb⟩ := key a ha
    obtain ⟨u, hu⟩ := hsu
    have e : algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s) *
        algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) =
        algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) *
          algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b) := by
      simp only [← map_mul, hb]
    rw [← hu] at e
    refine Ideal.mem_span_singleton.mpr ⟨algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b) * ↑u⁻¹, ?_⟩
    calc algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a)
        = ↑u⁻¹ * (↑u * algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a)) := by simp
      _ = ↑u⁻¹ * (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) *
          algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b)) := by rw [e]
      _ = _ := by ring
  have hm : IsLocalRing.maximalIdeal (Op D N la) =
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      have hle : laT D N la ≤ Ideal.comap (algebraMap (OT K D N) (Op D N la))
          (Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)}) := by
        show Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal ≤ _
        refine Ideal.map_le_iff_le_comap.mpr ?_
        intro a ha
        exact hsub a ha
      exact hle
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hϖ)
  set x := algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) with hxdef
  have hx0 : x ≠ 0 := by
    have hϖ0 : ϖ ≠ 0 := fun h => hϖ2 (h ▸ Ideal.zero_mem _)
    rw [hxdef]
    refine (map_ne_zero_iff _ (IsLocalization.injective (Op D N la)
      (Ideal.primeCompl_le_nonZeroDivisors (laT D N la)))).mpr ?_
    simpa using hϖ0
  have hxm : x ∈ IsLocalRing.maximalIdeal (Op D N la) := by
    rw [hm]
    exact Ideal.mem_span_singleton_self x
  haveI : IsNoetherianRing (Op D N la) := by
    first
      | infer_instance
      | exact IsLocalization.isNoetherianRing (laT D N la).primeCompl (Op D N la) inferInstance
  have hnf : ¬ IsField (Op D N la) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro h
    apply hx0
    rw [h] at hxm
    exact Ideal.mem_bot.mp hxm
  have hprinc : (IsLocalRing.maximalIdeal (Op D N la)).IsPrincipal := ⟨⟨x, hm⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Op D N la) hnf).out 4 2).mp hprinc
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
    letI := algOpKT (K := K) d.D d.N la
    IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) ∧
      IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      IsDedekindDomain (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) ∧
      IsFractionRing (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) (OmS (Ω c) d.D d.N) := by
  classical
  letI iKS : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iOS : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  letI iOK : Algebra (Op d.D d.N la) (KTf K d.D d.N) := algOpKT (K := K) d.D d.N la
  haveI hF : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := op_isFractionRing' d.D d.N la
  haveI hT : IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  haveI hFD : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    obtain ⟨_, _, hsp⟩ := hd.a4.choose_spec
    refine Module.finite_def.mpr ⟨Finset.univ.image (fun k => d.bvecG hd.sel hd.a4.choose k c),
      eq_top_iff.mpr fun y _ => ?_⟩
    obtain ⟨q, hq, p, hp⟩ := hsp (Pi.single c y)
    have hy := hp c
    rw [Pi.single_eq_same] at hy
    have hq' := hq c
    have hS : ∀ r : KTp K d.D d.N,
        d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) r) = d.sH c r := by
      intro r
      unfold Data.KTtoS
      exact IsFractionRing.lift_algebraMap _ _
    have hyy : y = ∑ k, (algebraMap _ (KTf K d.D d.N) (p k) / algebraMap _ (KTf K d.D d.N) q) •
        d.bvecG hd.sel hd.a4.choose k c := by
      show y = ∑ k, d.KTtoS h c (algebraMap _ (KTf K d.D d.N) (p k) /
        algebraMap _ (KTf K d.D d.N) q) * d.bvecG hd.sel hd.a4.choose k c
      simp only [map_div₀, hS]
      calc y = (d.sH c q)⁻¹ * (d.sH c q * y) := by
            rw [← mul_assoc, inv_mul_cancel₀ hq', one_mul]
        _ = (d.sH c q)⁻¹ * ∑ k, d.sH c (p k) * d.bvecG hd.sel hd.a4.choose k c :=
            congrArg (fun t => (d.sH c q)⁻¹ * t) hy
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
    rw [hyy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  haveI hsep : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := inferInstance
  haveI : IsDedekindDomain (Op d.D d.N la) := isDedekindDomain_Op d.D d.N la
  refine ⟨hF, hT, hFD, hsep, ?_, ?_⟩
  · first
      | exact integralClosure.isDedekindDomain (A := Op d.D d.N la) (K := KTf K d.D d.N)
          (L := OmS (Ω c) d.D d.N)
      | exact integralClosure.isDedekindDomain (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
  · first
      | exact integralClosure.isFractionRing_of_finite_extension (A := Op d.D d.N la)
          (K := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N)
      | exact integralClosure.isFractionRing_of_finite_extension (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
end ReciprocityTheory.ChartRestriction.G.T0.Data
