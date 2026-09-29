-- Prove2me | solution 1 for TaoFivePrimes.local_L2_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T02:12:27.46692+00:00
-- url     : https://prove2.me/submissions/7c18bacc-ca11-4cd3-976c-bc07db5a413c

import Mathlib
import Theorems.Thm_TaoFivePrimes_mertens_coprime_split
import Theorems.Thm_TaoFivePrimes_farey_rough_separation
import Theorems.Thm_TaoFivePrimes_log_le_sum_moebius_sq_div_totient

open Finset MeasureTheory

section PartL46C
open Finset MeasureTheory
namespace TaoL46C

noncomputable def wt (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℝ)) ^ 2 / (Nat.totient n : ℝ)

/-- The radius of the Farey neighbourhoods. -/
noncomputable def rad (Q R : ℕ) : ℝ := 1 / (2 * (Q : ℝ) ^ 2 * (R : ℝ) ^ 2)

/-- The Farey neighbourhood system `Σ`. -/
def Sig (Q R : ℕ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ q0 ∈ Finset.Icc 1 Q, ⋃ a0 ∈ Finset.range q0,
    Metric.ball ((((a0 : ℝ) / q0 : ℝ) : AddCircle (1 : ℝ))) (rad Q R)

/-- The translate `Σ + c`. -/
def Tr (Q R : ℕ) (c : AddCircle (1 : ℝ)) : Set (AddCircle (1 : ℝ)) :=
  (fun β => β - c) ⁻¹' Sig Q R

theorem isOpen_Sig (Q R : ℕ) : IsOpen (Sig Q R) :=
  isOpen_biUnion (fun _ _ => isOpen_biUnion (fun _ _ => Metric.isOpen_ball))

theorem measurable_Sig (Q R : ℕ) : MeasurableSet (Sig Q R) := (isOpen_Sig Q R).measurableSet

theorem measurable_Tr (Q R : ℕ) (c : AddCircle (1 : ℝ)) : MeasurableSet (Tr Q R c) :=
  ((isOpen_Sig Q R).preimage (continuous_id.sub continuous_const)).measurableSet

theorem mem_Tr_iff {Q R : ℕ} {c β : AddCircle (1 : ℝ)} :
    β ∈ Tr Q R c ↔ ∃ q0 ∈ Finset.Icc 1 Q, ∃ a0 ∈ Finset.range q0,
      ‖β - c - (((a0 : ℝ) / q0 : ℝ) : AddCircle (1 : ℝ))‖ < rad Q R := by
  simp only [Tr, Sig, Set.mem_preimage, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm,
    exists_prop]

/-- The norm on the unit circle, in terms of the distance to the nearest integer. -/
theorem norm_coe (x : ℝ) : ‖((x : ℝ) : AddCircle (1 : ℝ))‖ = |x - round x| := by
  rw [AddCircle.norm_eq]
  norm_num

/-- Distinct reduced fractions with `Q`-rough denominators at most `R` translate `Σ` to
disjoint sets. -/
theorem Tr_disjoint (Q R : ℕ) (q1 a1 q1' a1' : ℕ)
    (hq1 : 0 < q1) (hq1R : q1 ≤ R) (hr1 : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1)
    (ha1 : a1 < q1) (hc1 : Nat.Coprime a1 q1)
    (hq1' : 0 < q1') (hq1'R : q1' ≤ R) (hr1' : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1')
    (ha1' : a1' < q1') (hc1' : Nat.Coprime a1' q1')
    (hne : ¬ (q1 = q1' ∧ a1 = a1')) :
    Disjoint (Tr Q R (((a1 : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ)))
      (Tr Q R (((a1' : ℝ) / q1' : ℝ) : AddCircle (1 : ℝ))) := by
  rw [Set.disjoint_left]
  intro β hβ hβ'
  obtain ⟨q0, hq0m, a0, ha0m, h1⟩ := mem_Tr_iff.mp hβ
  obtain ⟨q0', hq0'm, a0', ha0'm, h2⟩ := mem_Tr_iff.mp hβ'
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective β
  rw [Finset.mem_Icc] at hq0m hq0'm
  rw [Finset.mem_range] at ha0m ha0'm
  set v1 : ℝ := u - (a1 : ℝ) / q1 - (a0 : ℝ) / q0 with hv1
  set v2 : ℝ := u - (a1' : ℝ) / q1' - (a0' : ℝ) / q0' with hv2
  have e1 : ((u : ℝ) : AddCircle (1 : ℝ)) - (((a1 : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ))
      - (((a0 : ℝ) / q0 : ℝ) : AddCircle (1 : ℝ)) = ((v1 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [hv1, AddCircle.coe_sub, AddCircle.coe_sub]
  have e2 : ((u : ℝ) : AddCircle (1 : ℝ)) - (((a1' : ℝ) / q1' : ℝ) : AddCircle (1 : ℝ))
      - (((a0' : ℝ) / q0' : ℝ) : AddCircle (1 : ℝ)) = ((v2 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [hv2, AddCircle.coe_sub, AddCircle.coe_sub]
  rw [e1, norm_coe] at h1
  rw [e2, norm_coe] at h2
  -- the Farey separation applies
  have hxk : ∃ k : ℤ,
      |((a0 : ℝ) / q0 + (a1 : ℝ) / q1 - (a0' : ℝ) / q0' - (a1' : ℝ) / q1') - (k : ℝ)|
        < 1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2) := by
    refine ⟨round v2 - round v1, ?_⟩
    have hx : ((a0 : ℝ) / q0 + (a1 : ℝ) / q1 - (a0' : ℝ) / q0' - (a1' : ℝ) / q1')
        - ((round v2 - round v1 : ℤ) : ℝ)
        = (v2 - round v2) - (v1 - round v1) := by
      rw [hv1, hv2]; push_cast; ring
    have hQR : (0 : ℝ) < (Q : ℝ) ^ 2 * (R : ℝ) ^ 2 := by
      have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by
        have : 1 ≤ q0 := hq0m.1
        have : (1 : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast this
        have h2' : (q0 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq0m.2
        linarith
      have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
        have : (1 : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hq1
        have h2' : (q1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hq1R
        linarith
      positivity
    have hrad : rad Q R * 2 = 1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2) := by
      rw [rad]; field_simp
    rw [hx]
    calc |(v2 - round v2) - (v1 - round v1)|
        ≤ |v2 - (round v2 : ℝ)| + |v1 - (round v1 : ℝ)| := abs_sub _ _
      _ < rad Q R + rad Q R := by linarith [h1, h2]
      _ = 1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2) := by rw [← hrad]; ring
  have hdvd := TaoFivePrimes.farey_rough_separation Q R q0 q0' q1 q1'
    (a0 : ℤ) (a0' : ℤ) (a1 : ℤ) (a1' : ℤ)
    (by omega) hq0m.2 (by omega) hq0'm.2 hq1 hq1R hq1' hq1'R hr1 hr1'
    (by push_cast at hxk ⊢; exact hxk)
  -- the reduced fractions must coincide
  have hqq'pos : (0 : ℤ) < (q1 : ℤ) * q1' := by
    have h1' : (0 : ℤ) < (q1 : ℤ) := by exact_mod_cast hq1
    have h2' : (0 : ℤ) < (q1' : ℤ) := by exact_mod_cast hq1'
    positivity
  have hA : (a1 : ℤ) * q1' < (q1 : ℤ) * q1' := by
    have h3 : (a1 : ℤ) < q1 := by exact_mod_cast ha1
    have hq' : (0 : ℤ) < (q1' : ℤ) := by exact_mod_cast hq1'
    exact mul_lt_mul_of_pos_right h3 hq'
  have hB : (a1' : ℤ) * q1 < (q1' : ℤ) * q1 := by
    have h4 : (a1' : ℤ) < q1' := by exact_mod_cast ha1'
    have hq' : (0 : ℤ) < (q1 : ℤ) := by exact_mod_cast hq1
    exact mul_lt_mul_of_pos_right h4 hq'
  have hA0 : (0 : ℤ) ≤ (a1 : ℤ) * q1' := by positivity
  have hB0 : (0 : ℤ) ≤ (a1' : ℤ) * q1 := by positivity
  have hlo : -((q1 : ℤ) * q1') < (a1 : ℤ) * q1' - (a1' : ℤ) * q1 := by nlinarith
  have hhi : (a1 : ℤ) * q1' - (a1' : ℤ) * q1 < (q1 : ℤ) * q1' := by nlinarith
  have hzero : (a1 : ℤ) * q1' - (a1' : ℤ) * q1 = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    rcases lt_trichotomy t 0 with h | h | h
    · exfalso
      have hle : (a1 : ℤ) * q1' - (a1' : ℤ) * q1 ≤ -((q1 : ℤ) * q1') := by
        rw [ht]; nlinarith
      linarith
    · rw [ht, h, mul_zero]
    · exfalso
      have hge : (q1 : ℤ) * q1' ≤ (a1 : ℤ) * q1' - (a1' : ℤ) * q1 := by
        rw [ht]; nlinarith
      linarith
  have heq : a1 * q1' = a1' * q1 := by
    have : (a1 : ℤ) * q1' = (a1' : ℤ) * q1 := by omega
    exact_mod_cast this
  have hd1 : q1 ∣ q1' := by
    have : q1 ∣ a1 * q1' := ⟨a1', by rw [heq]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left hc1.symm this)
  have hd2 : q1' ∣ q1 := by
    have : q1' ∣ a1' * q1 := ⟨a1, by rw [← heq]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left hc1'.symm this)
  have hqq : q1 = q1' := Nat.dvd_antisymm hd1 hd2
  subst hqq
  have : a1 = a1' := by
    have := heq
    exact Nat.eq_of_mul_eq_mul_right hq1 this
  exact hne ⟨rfl, this⟩

/-- Translating the region of integration. -/
theorem setIntegral_shift (Q R : ℕ) (c : AddCircle (1 : ℝ)) (f : AddCircle (1 : ℝ) → ℝ) :
    (∫ α in Sig Q R, f (α + c) ∂AddCircle.haarAddCircle)
      = ∫ β in Tr Q R c, f β ∂AddCircle.haarAddCircle := by
  have hmp : MeasurePreserving (fun α : AddCircle (1 : ℝ) => α + c)
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
    measurePreserving_add_right _ c
  have hemb : MeasurableEmbedding (fun α : AddCircle (1 : ℝ) => α + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have hpre : (fun α : AddCircle (1 : ℝ) => α + c) ⁻¹' (Tr Q R c) = Sig Q R := by
    ext α
    simp [Tr, Set.mem_preimage]
  have h := hmp.setIntegral_preimage_emb hemb f (Tr Q R c)
  rw [hpre] at h
  exact h

/-- The `Q`-rough moduli up to `R`. -/
def Rough (Q R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter
    (fun m => Nat.Coprime m (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, p))

/-- The reduced residues mod `q`. -/
def Cop (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- The index set of Farey translations. -/
def Tidx (Q R : ℕ) : Finset (ℕ × ℕ) :=
  (Rough Q R).biUnion (fun q => (Cop q).image (fun a => (q, a)))

theorem rough_prime {Q R q : ℕ} (hq : q ∈ Rough Q R) :
    ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q := by
  intro p hp hpQ hpd
  have hc : Nat.Coprime q (∏ r ∈ (Finset.Icc 1 Q).filter Nat.Prime, r) :=
    (Finset.mem_filter.mp hq).2
  have hmem : p ∈ (Finset.Icc 1 Q).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hpQ⟩, hp⟩
  have hpP : p ∣ ∏ r ∈ (Finset.Icc 1 Q).filter Nat.Prime, r := Finset.dvd_prod_of_mem _ hmem
  have : p ∣ Nat.gcd q (∏ r ∈ (Finset.Icc 1 Q).filter Nat.Prime, r) := Nat.dvd_gcd hpd hpP
  rw [show Nat.gcd q (∏ r ∈ (Finset.Icc 1 Q).filter Nat.Prime, r) = 1 from hc] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem rough_bounds {Q R q : ℕ} (hq : q ∈ Rough Q R) : 0 < q ∧ q ≤ R := by
  have := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
  exact ⟨by omega, this.2⟩

theorem mem_Tidx {Q R : ℕ} {z : ℕ × ℕ} :
    z ∈ Tidx Q R ↔ z.1 ∈ Rough Q R ∧ z.2 ∈ Cop z.1 := by
  simp only [Tidx, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, a, ha, rfl⟩
    exact ⟨hq, ha⟩
  · rintro ⟨h1, h2⟩
    exact ⟨z.1, h1, z.2, h2, rfl⟩

/-- **Tao, Lemma 4.6 (Local `L²` estimate)**, deduced from Montgomery's uncertainty
principle (Lemma 4.4), quoted here as the hypothesis `hmup`. -/
theorem local_L2 (Q R : ℕ) (hQ : 1 ≤ Q) (hR : 1 ≤ R)
    (f : AddCircle (1 : ℝ) → ℝ) (hf0 : ∀ α, 0 ≤ f α)
    (hfi : Integrable f AddCircle.haarAddCircle)
    (hmup : ∀ q1 : ℕ, 0 < q1 → q1 ≤ R → ∀ α : AddCircle (1 : ℝ),
      wt q1 * f α ≤ ∑ a ∈ Cop q1, f (α + (((a : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ)))) :
    Real.log R * (∫ α in Sig Q R, f α ∂AddCircle.haarAddCircle)
      ≤ (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1)))
        * ∫ α, f α ∂AddCircle.haarAddCircle := by
  classical
  have hshiftint : ∀ c : AddCircle (1 : ℝ),
      Integrable (fun α => f (α + c)) AddCircle.haarAddCircle := by
    intro c
    have hmp : MeasurePreserving (fun α : AddCircle (1 : ℝ) => α + c)
        AddCircle.haarAddCircle AddCircle.haarAddCircle := measurePreserving_add_right _ c
    exact (hmp.integrable_comp_emb ((Homeomorph.addRight c).measurableEmbedding)).mpr hfi
  set I : ℝ := ∫ α in Sig Q R, f α ∂AddCircle.haarAddCircle with hIdef
  set B : ℝ := ∫ α, f α ∂AddCircle.haarAddCircle with hBdef
  set Pr : ℝ := ∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1)) with hPrdef
  have hI0 : 0 ≤ I := setIntegral_nonneg (measurable_Sig Q R) (fun x _ => hf0 x)
  have hPr0 : 0 ≤ Pr := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  -- Step A: Montgomery, integrated over `Σ`
  have hA : ∀ q1 ∈ Rough Q R, wt q1 * I ≤ ∑ a ∈ Cop q1,
      ∫ β in Tr Q R ((((a : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ))), f β ∂AddCircle.haarAddCircle := by
    intro q1 hq1
    obtain ⟨hq1pos, hq1R⟩ := rough_bounds hq1
    have hmono : (∫ α in Sig Q R, wt q1 * f α ∂AddCircle.haarAddCircle)
        ≤ ∫ α in Sig Q R,
            (∑ a ∈ Cop q1, f (α + (((a : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ))))
              ∂AddCircle.haarAddCircle := by
      refine setIntegral_mono_on (hfi.const_mul _).integrableOn ?_ (measurable_Sig Q R)
        (fun x _ => hmup q1 hq1pos hq1R x)
      exact (integrable_finset_sum _ (fun a _ => hshiftint _)).integrableOn
    rw [integral_const_mul,
      integral_finset_sum _ (fun a _ => (hshiftint _).integrableOn)] at hmono
    calc wt q1 * I ≤ ∑ a ∈ Cop q1,
            ∫ α in Sig Q R, f (α + (((a : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ)))
              ∂AddCircle.haarAddCircle := hmono
      _ = _ := Finset.sum_congr rfl (fun a _ => setIntegral_shift Q R _ f)
  -- disjointness of the translates
  have hdisj : (↑(Tidx Q R) : Set (ℕ × ℕ)).Pairwise
      (Function.onFun Disjoint
        (fun z : ℕ × ℕ => Tr Q R ((((z.2 : ℝ) / z.1 : ℝ) : AddCircle (1 : ℝ))))) := by
    intro z hz z' hz' hne
    obtain ⟨hz1, hz2⟩ := mem_Tidx.mp (Finset.mem_coe.mp hz)
    obtain ⟨hz'1, hz'2⟩ := mem_Tidx.mp (Finset.mem_coe.mp hz')
    obtain ⟨hp1, hb1⟩ := rough_bounds hz1
    obtain ⟨hp1', hb1'⟩ := rough_bounds hz'1
    have hc1 := Finset.mem_filter.mp hz2
    have hc1' := Finset.mem_filter.mp hz'2
    refine Tr_disjoint Q R z.1 z.2 z'.1 z'.2 hp1 hb1 (rough_prime hz1)
      (Finset.mem_range.mp hc1.1) hc1.2 hp1' hb1' (rough_prime hz'1)
      (Finset.mem_range.mp hc1'.1) hc1'.2 ?_
    rintro ⟨h1, h2⟩
    exact hne (Prod.ext h1 h2)
  -- Step B: the translates fit inside the whole circle
  have hB2 : (∑ z ∈ Tidx Q R,
      ∫ β in Tr Q R ((((z.2 : ℝ) / z.1 : ℝ) : AddCircle (1 : ℝ))), f β ∂AddCircle.haarAddCircle)
      ≤ B := by
    rw [← integral_biUnion_finset (Tidx Q R) (fun z _ => measurable_Tr Q R _) hdisj
      (fun z _ => hfi.integrableOn)]
    exact setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)
  -- reindexing the double sum
  have hfib : ∀ q ∈ Rough Q R, ∀ q' ∈ Rough Q R, q ≠ q' →
      Disjoint ((Cop q).image (fun a => (q, a))) ((Cop q').image (fun a => (q', a))) := by
    intro q _ q' _ hqq
    rw [Finset.disjoint_left]
    rintro z hz hz'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hz'
    exact hqq (congrArg Prod.fst hb).symm
  have hsum : (∑ q ∈ Rough Q R, ∑ a ∈ Cop q,
        ∫ β in Tr Q R ((((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ))), f β ∂AddCircle.haarAddCircle)
      = ∑ z ∈ Tidx Q R,
          ∫ β in Tr Q R ((((z.2 : ℝ) / z.1 : ℝ) : AddCircle (1 : ℝ))), f β
            ∂AddCircle.haarAddCircle := by
    rw [Tidx, Finset.sum_biUnion hfib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.injEq _ _ _ _ ▸ h : q = q ∧ a = b).2)]
  -- the weighted sum
  have hWI : (∑ q ∈ Rough Q R, wt q) * I ≤ B := by
    rw [Finset.sum_mul]
    calc (∑ q ∈ Rough Q R, wt q * I)
        ≤ ∑ q ∈ Rough Q R, ∑ a ∈ Cop q,
            ∫ β in Tr Q R ((((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ))), f β
              ∂AddCircle.haarAddCircle := Finset.sum_le_sum hA
      _ = _ := hsum
      _ ≤ B := hB2
  -- the arithmetic input
  have hlogle : Real.log R ≤ (∑ q ∈ Rough Q R, wt q) * Pr := by
    have h1 := TaoFivePrimes.log_le_sum_moebius_sq_div_totient (R : ℝ) (by positivity)
    rw [Nat.floor_natCast] at h1
    have h2 := TaoFivePrimes.mertens_coprime_split Q R
    simp only [wt, Rough, hPrdef]
    linarith [h1, h2]
  calc Real.log R * I ≤ ((∑ q ∈ Rough Q R, wt q) * Pr) * I :=
        mul_le_mul_of_nonneg_right hlogle hI0
    _ = Pr * ((∑ q ∈ Rough Q R, wt q) * I) := by ring
    _ ≤ Pr * B := mul_le_mul_of_nonneg_left hWI hPr0

end TaoL46C
end PartL46C

theorem solution (Q R : ℕ) (hQ : 1 ≤ Q) (hR : 1 ≤ R)
    (f : AddCircle (1 : ℝ) → ℝ) (hf0 : ∀ α, 0 ≤ f α)
    (hfi : MeasureTheory.Integrable f AddCircle.haarAddCircle)
    (hmup : ∀ q1 : ℕ, 0 < q1 → q1 ≤ R → ∀ α : AddCircle (1 : ℝ),
      ((ArithmeticFunction.moebius q1 : ℝ)) ^ 2 / (Nat.totient q1 : ℝ) * f α
        ≤ ∑ a ∈ (Finset.range q1).filter (fun a => Nat.Coprime a q1),
            f (α + (((a : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ)))) :
    Real.log R *
        (∫ α in (⋃ q0 ∈ Finset.Icc 1 Q, ⋃ a0 ∈ Finset.range q0,
              Metric.ball ((((a0 : ℝ) / q0 : ℝ) : AddCircle (1 : ℝ)))
                (1 / (2 * (Q : ℝ) ^ 2 * (R : ℝ) ^ 2))),
            f α ∂AddCircle.haarAddCircle)
      ≤ (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1)))
        * ∫ α, f α ∂AddCircle.haarAddCircle :=
  TaoL46C.local_L2 Q R hQ hR f hf0 hfi hmup
