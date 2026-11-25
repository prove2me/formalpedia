-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.norm_by_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:08.248496+00:00
-- url     : https://prove2.me/submissions/bd1a3165-e6f6-4d1f-a79d-f7774db858c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_omS_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_fin_support
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_local_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private lemma span_singleton_mem_htOne_of_prime {π : KTp K d.D d.N} (hπ : Prime π) : Ideal.span {π} ∈ d.HtOne := by
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  haveI := hP
  refine ⟨hP, le_antisymm ?_ ?_⟩
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by norm_num, Ideal.height_le_iff]
    intro q hq hlt
    haveI := hq
    by_cases hqb : q = ⊥
    · subst hqb
      rw [Ideal.height_bot]
      norm_num
    · exfalso
      obtain ⟨π', hπ'q, hπ'⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hq hqb
      have h1 : π' ∈ Ideal.span {π} := hlt.le hπ'q
      rw [Ideal.mem_span_singleton] at h1
      obtain ⟨t, ht⟩ := h1
      rcases hπ'.dvd_or_dvd (dvd_of_eq ht) with h | h
      · have hmem : π ∈ q := by
          obtain ⟨r, hr⟩ := h
          rw [hr]
          exact q.mul_mem_right _ hπ'q
        exact hlt.not_ge ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      · obtain ⟨r, hr⟩ := h
        have e : π' * (π * r) = π' * 1 := by
          rw [mul_one]
          conv_rhs => rw [ht, hr]
          ring
        exact hπ.not_unit (isUnit_iff_exists_inv.mpr ⟨r, mul_left_cancel₀ hπ'.ne_zero e⟩)
  · by_contra hlt
    push_neg at hlt
    have h0 : (Ideal.span {π}).height ≤ ((0 : ℕ) : ℕ∞) := by
      simpa using ENat.lt_one_iff_eq_zero.mp hlt
    rw [Ideal.height_le_iff] at h0
    have h2 := h0 ⊥ Ideal.bot_prime (by
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hπ.ne_zero)
    simp at h2
private lemma gen_notMem_of_ne {p q : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (hq : q ∈ d.HtOne)
    (hne : q ≠ p) : d.gen q ∉ p := by
  intro hg
  have hle : q ≤ p := by
    rw [d.gen_span hq]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hg
  haveI := hp.1
  have h1 := (Ideal.height_le_iff (n := 1)).mp (by rw [hp.2]; norm_num) q hq.1 (lt_of_le_of_ne hle hne)
  rw [hq.2] at h1
  norm_num at h1
private lemma exists_const_of_locally_unit_at_htOne (u : KTf K d.D d.N) (hu : u ≠ 0)
    (hloc : ∀ p ∈ d.HtOne, ∃ a s : KTp K d.D d.N, a ∉ p ∧ s ∉ p ∧
      u * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) :
    ∃ κ : K, κ ≠ 0 ∧ u = algebraMap K (KTf K d.D d.N) κ := by
  have hred := IsFractionRing.num_den_reduced (KTp K d.D d.N) u
  have heq := IsFractionRing.mk'_num_den' (KTp K d.D d.N) u
  set n := IsFractionRing.num (KTp K d.D d.N) u with hn_def
  set m := IsFractionRing.den (KTp K d.D d.N) u with hm_def
  have hm0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (m : KTp K d.D d.N) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors m.2
  have hnu : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) n =
      u * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (m : KTp K d.D d.N) := by
    rw [← heq, div_mul_cancel₀ _ hm0]
  have hcross : ∀ a s : KTp K d.D d.N,
      u * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a →
      n * s = a * (m : KTp K d.D d.N) := by
    intro a s has
    apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    rw [map_mul, map_mul, hnu, ← has]
    ring
  have hn0 : n ≠ 0 := by
    intro h0
    apply hu
    rw [← heq, h0, map_zero, zero_div]
  have hm0' : (m : KTp K d.D d.N) ≠ 0 := nonZeroDivisors.coe_ne_zero m
  have hunit : ∀ x : KTp K d.D d.N, x ≠ 0 → (x = n ∨ x = m) → IsUnit x := by
    intro x hx0 hx
    by_contra hxu
    obtain ⟨π, hirr, hπx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
    have hπ : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    obtain ⟨a, s, ha, hs, has⟩ := hloc _ (span_singleton_mem_htOne_of_prime d hπ)
    have hR := hcross a s has
    have hπa : ¬ π ∣ a := fun h => ha (Ideal.mem_span_singleton.mpr h)
    have hπs : ¬ π ∣ s := fun h => hs (Ideal.mem_span_singleton.mpr h)
    rcases hx with rfl | rfl
    · have h1 : π ∣ a * m := hR ▸ dvd_mul_of_dvd_left hπx s
      rcases hπ.dvd_or_dvd h1 with h | h
      · exact hπa h
      · exact hπ.not_unit (hred hπx h)
    · have h1 : π ∣ n * s := hR.symm ▸ dvd_mul_of_dvd_right hπx a
      rcases hπ.dvd_or_dvd h1 with h | h
      · exact hπ.not_unit (hred h hπx)
      · exact hπs h
  obtain ⟨r1, hr1, hn⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (hunit n hn0 (Or.inl rfl))
  obtain ⟨r2, hr2, hm⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (hunit _ hm0' (Or.inr rfl))
  have hC : ∀ r : K, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C r) =
      algebraMap K (KTf K d.D d.N) r := fun r => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  refine ⟨r1 / r2, div_ne_zero hr1.ne_zero hr2.ne_zero, ?_⟩
  rw [← heq, hn, hm, hC, hC, map_div₀]
private lemma prod_gen_zpow_split_at {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (E : Ideal (KTp K d.D d.N) → ℤ)
    (T : Finset (Ideal (KTp K d.D d.N))) (hT : ∀ q ∈ T, q ∈ d.HtOne) :
    ∃ A B : KTp K d.D d.N, A ∉ p ∧ B ∉ p ∧
      (∏ q ∈ T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) *
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) B =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ (if p ∈ T then E p else 0) *
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A := by
  classical
  have h1p : (1 : KTp K d.D d.N) ∉ p := (Ideal.ne_top_iff_one p).mp hp.1.ne_top
  induction T using Finset.induction_on with
  | empty => exact ⟨1, 1, h1p, h1p, by simp⟩
  | insert q T hqT ih =>
    obtain ⟨A, B, hA, hB, hAB⟩ := ih (fun q' h => hT q' (Finset.mem_insert_of_mem h))
    have hqH : q ∈ d.HtOne := hT q (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hqT]
    by_cases hqp : q = p
    · subst hqp
      refine ⟨A, B, hA, hB, ?_⟩
      rw [if_pos (Finset.mem_insert_self _ _), mul_assoc, hAB, if_neg hqT, zpow_zero, one_mul]
    · have hgq : d.gen q ∉ p := gen_notMem_of_ne d hp hqH hqp
      have hgq0 : d.gen q ≠ 0 := by
        intro h0
        have hq := d.gen_span hqH
        rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hq
        have h2 := hqH.2
        rw [hq, Ideal.height_bot] at h2
        exact zero_ne_one h2
      have hg0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ≠ 0 := by
        rw [Ne, IsFractionRing.to_map_eq_zero_iff]
        exact hgq0
      have hnot : ∀ (X : KTp K d.D d.N) (k : ℕ), X ∉ p → X * d.gen q ^ k ∉ p := fun X k hX h =>
        (hp.1.mem_or_mem h).elim hX (fun h' => hgq (hp.1.mem_of_pow_mem _ h'))
      have hif : (if p ∈ insert q T then E p else 0) = (if p ∈ T then E p else 0) := by
        simp [Finset.mem_insert, Ne.symm hqp]
      rw [hif]
      rcases le_or_gt 0 (E q) with hE | hE
      · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hE
        refine ⟨A * d.gen q ^ k, B, hnot A k hA, hB, ?_⟩
        rw [hk, zpow_natCast, map_mul, map_pow, mul_assoc, hAB]
        ring
      · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hE.le
        refine ⟨A, B * d.gen q ^ k, hA, hnot B k hB, ?_⟩
        rw [hk, zpow_neg, zpow_natCast, map_mul, map_pow]
        calc (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ k)⁻¹ *
              (∏ q ∈ T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) *
              (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) B *
                algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ k)
            = (∏ q ∈ T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) *
                algebraMap (KTp K d.D d.N) (KTf K d.D d.N) B *
                ((algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ k)⁻¹ *
                  algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ k) := by ring
          _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ hg0), mul_one, hAB]
private lemma overP_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N))
    (hp : p ∈ d.HtOne) : (d.OverP c p).Finite := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hmap : ∀ x : KTp K d.D d.N, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) = d.sH c x := by
    intro x
    exact IsFractionRing.lift_algebraMap (h c) x
  have hOver : d.OverP c p = HNm.OverR (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) p := by
    ext w
    simp only [Data.OverP, HNm.OverR, Set.mem_setOf_eq, hmap]
  obtain ⟨hprime, hh⟩ := hp
  haveI := hprime
  rw [hOver]
  exact (HNm.local_norm (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) p hh
    (d.gen p) (d.gen_span ⟨hprime, hh⟩) 1 one_ne_zero).1
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    (∀ p ∈ d.HtOne, (d.OverP c p).Finite) ∧
    ∀ y : OmS (Ω c) d.D d.N, y ≠ 0 →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0}.Finite ∧
      ∃ κ : K, κ ≠ 0 ∧
        letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
        Algebra.norm (KTf K d.D d.N) y =
          algebraMap K (KTf K d.D d.N) κ *
            ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
              algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
                (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
                  (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hmap : ∀ x : KTp K d.D d.N, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) = d.sH c x := by
    intro x
    exact IsFractionRing.lift_algebraMap (h c) x
  have hOver : ∀ p, d.OverP c p =
      HNm.OverR (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) p := by
    intro p
    ext w
    simp only [Data.OverP, HNm.OverR, Set.mem_setOf_eq, hmap]
  refine ⟨fun p hp => overP_finite d hd h c p hp, fun y hy => ?_⟩
  have hset : {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0} =
      {p : Ideal (KTp K d.D d.N) | p.IsPrime ∧ p.height = 1 ∧
        ∃ w ∈ HNm.OverR (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) p, w y ≠ 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Data.HtOne, hOver, and_assoc]
  have hfin : {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0}.Finite := by
    rw [hset]
    exact HNm.fin_support (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) y hy
  refine ⟨hfin, ?_⟩
  classical
  set E : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (w y) with hE_def
  set T := hfin.toFinset with hT_def
  have hTsub : ∀ q ∈ T, q ∈ d.HtOne := fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1
  have hE0 : ∀ p ∈ d.HtOne, p ∉ T → E p = 0 := by
    intro p hp hpT
    have hz : ∀ w ∈ d.OverP c p, w y = 0 := by
      intro w hw
      by_contra hne
      exact hpT ((Set.Finite.mem_toFinset _).mpr ⟨hp, w, hw, hne⟩)
    rw [hE_def]
    apply finsum_eq_zero_of_forall_eq_zero
    intro w
    by_cases hw : w ∈ d.OverP c p
    · simp [hw, hz w hw]
    · simp [hw]
  set z := Algebra.norm (KTf K d.D d.N) y with hz_def
  have hz0 : z ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  set P := ∏ q ∈ T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q with hP_def
  have hP0 : P ≠ 0 := by
    rw [hP_def, Finset.prod_ne_zero_iff]
    intro q hq
    apply zpow_ne_zero
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    intro h0
    have hqH := hTsub q hq
    have hq' := d.gen_span hqH
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hq'
    have h2 := hqH.2
    rw [hq', Ideal.height_bot] at h2
    exact zero_ne_one h2
  have hloc : ∀ p ∈ d.HtOne, ∃ a s : KTp K d.D d.N, a ∉ p ∧ s ∉ p ∧
      z / P * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a := by
    intro p hp
    haveI := hp.1
    obtain ⟨-, a, s, ha, hs, hzs⟩ := HNm.local_norm (R := KTp K d.D d.N) (F := KTf K d.D d.N)
      (L := OmS (Ω c) d.D d.N) p hp.2 (d.gen p) (d.gen_span hp) y hy
    rw [← hOver p] at hzs
    change z * _ = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p * _ at hzs
    obtain ⟨A, B, hA, hB, hAB⟩ := prod_gen_zpow_split_at d hp E T hTsub
    have hexp : (if p ∈ T then E p else 0) = E p := by
      split_ifs with hpT
      · rfl
      · exact (hE0 p hp hpT).symm
    rw [hexp] at hAB
    refine ⟨a * B, s * A, fun h' => (hp.1.mem_or_mem h').elim ha hB,
      fun h' => (hp.1.mem_or_mem h').elim hs hA, ?_⟩
    have key : z * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) B * P := by
      rw [hzs]
      calc algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A
          = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a *
            (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p *
              algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A) := by ring
        _ = _ := by rw [← hAB]; ring
    rw [map_mul, map_mul]
    calc z / P * (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A)
        = z * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A / P := by
          ring
      _ = _ := by rw [key, mul_div_cancel_right₀ _ hP0]
  obtain ⟨κ, hκ, hu⟩ := exists_const_of_locally_unit_at_htOne d (z / P) (div_ne_zero hz0 hP0) hloc
  refine ⟨κ, hκ, ?_⟩
  have hfp : ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p = P := by
    rw [hP_def]
    apply finprod_mem_eq_prod_of_subset
    · rintro p ⟨hpH, hp1⟩
      by_contra hpT
      exact hp1 (by simp only []; rw [hE0 p hpH hpT, zpow_zero])
    · exact fun q hq => hTsub q hq
  change z = algebraMap K (KTf K d.D d.N) κ * ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p
  rw [hfp, ← hu, div_mul_cancel₀ _ hP0]
end ReciprocityTheory.ChartRestriction.G.T0.Data
