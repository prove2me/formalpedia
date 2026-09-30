-- Prove2me | solution 1 for WeierstrassEllipticZeta.canonical_capped_chart_cost
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T13:50:18.647085+00:00
-- url     : https://prove2.me/submissions/1a3b7e04-5951-4727-a892-e0be8dc8e552

import Definitions.Def_WeierstrassEllipticZeta_CanonicalChartCost
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Tactic

noncomputable section
namespace WeierstrassEllipticZeta

private theorem minimal_local_length_ne_top
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I p : Ideal R) [p.IsPrime] (hp : p ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≠ ⊤ := by
  let A := Localization.AtPrime p
  let J := I.map (algebraMap R A)
  have hrad : J.radical = IsLocalRing.maximalIdeal A := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A p I hp,
      IsLocalization.AtPrime.map_eq_maximalIdeal p A]
  have hJ : J.IsPrimary := Ideal.isPrimary_of_isMaximal_radical (hrad ▸ inferInstance)
  have hdim : Ring.KrullDimLE 0 (A ⧸ J) := by
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro q hq
    rw [Ideal.minimalPrimes_eq_subsingleton hJ, Set.mem_singleton_iff] at hq
    rw [hq, hrad]
    infer_instance
  let : IsArtinianRing (A ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : IsArtinian A (A ⧸ J) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J))
  exact Module.length_ne_top

private theorem chart_length_values_finite (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (c : Fin 2) (z : ℂ) :
    (cappedChartLengthValues L S Q N T c z).Finite := by
  let I (i : Fin 3) := extensionChartJetIdeal L Q c (min (i.val * T) N)
  let f (i : Fin 3) (p : PrimeSpectrum (MvPolynomial (Fin 4) ℂ)) :=
    (Module.length (Localization.AtPrime p.asIdeal)
      ((Localization.AtPrime p.asIdeal) ⧸ (I i).map
        (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime p.asIdeal)))).toNat
  have hp (i : Fin 3) : {p : PrimeSpectrum (MvPolynomial (Fin 4) ℂ) |
      p.asIdeal ∈ (I i).minimalPrimes}.Finite :=
    ((I i).finite_minimalPrimes_of_isNoetherianRing _).preimage
      (fun _ _ _ _ h => PrimeSpectrum.ext h)
  apply (Set.finite_iUnion fun i => (hp i).image (f i)).subset
  rintro n ⟨i, p, _, hmin, _, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, p, hmin, rfl⟩

private theorem canonical_budget_at (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (Z : Finset ℂ)
    (c : Fin 2) (z : ℂ) (hz : z ∈ Z) (hc : S (extensionChartDenominator c) z ≠ 0) :
    ∃ B : CappedChartJetBudget L S Q N T (cappedChartCost L S Q N T c z) Z,
      B.chart = c ∧ B.z = z := by
  refine ⟨⟨c, z, hz, hc, ?_⟩, rfl, rfl⟩
  intro i p hp hpoint hmin hnext
  have hf := minimal_local_length_ne_top (MvPolynomial (Fin 4) ℂ)
    (extensionChartJetIdeal L Q c (min (i.val * T) N)) p hmin
  have hv : (Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ (extensionChartJetIdeal L Q c (min (i.val * T) N)).map
        (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime p)))).toNat ∈
        cappedChartLengthValues L S Q N T c z :=
    ⟨i, ⟨p, hp⟩, hpoint, hmin, hnext, rfl⟩
  have hle := (le_csSup (chart_length_values_finite L S Q N T c z).bddAbove hv).trans
    (le_max_right 1 _)
  change _ ≤ (cappedChartCost L S Q N T c z : ℕ∞)
  rw [← ENat.natCast_toNat hf]
  exact_mod_cast hle

private theorem canonical_cost_le_budget (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (Z : Finset ℂ)
    (e : ℕ) (he : 0 < e) (B : CappedChartJetBudget L S Q N T e Z) :
    cappedChartCost L S Q N T B.chart B.z ≤ e := by
  apply max_le (Nat.succ_le_of_lt he)
  apply csSup_le'
  rintro n ⟨i, p, hpoint, hmin, hnext, rfl⟩
  have h := B.length_le i p.asIdeal hpoint hmin hnext
  simpa using ENat.toNat_le_toNat h (by simp)


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (N T : ℕ) (Z : Finset ℂ) :
    (∀ (c : Fin 2) (z : ℂ),
      (cappedChartLengthValues L S Q N T c z).Finite ∧
      0 < cappedChartCost L S Q N T c z ∧
      (z ∈ Z → S (extensionChartDenominator c) z ≠ 0 →
        ∃ B : CappedChartJetBudget L S Q N T (cappedChartCost L S Q N T c z) Z,
          B.chart = c ∧ B.z = z)) ∧
    (∀ (e : ℕ), 0 < e → ∀ B : CappedChartJetBudget L S Q N T e Z,
      cappedChartCost L S Q N T B.chart B.z ≤ e) ∧
    (∀ (ι : Type) [Fintype ι] [Nonempty ι] (e : ι → ℕ),
      (∀ i, 0 < e i) → (∀ i, Nonempty (CappedChartJetBudget L S Q N T (e i) Z)) →
      ∃ (c : Fin 2) (z : ℂ), z ∈ Z ∧ S (extensionChartDenominator c) z ≠ 0 ∧
        Fintype.card ι * cappedChartCost L S Q N T c z ≤ ∑ i, e i) := by
  classical
  refine ⟨fun c z => ⟨chart_length_values_finite L S Q N T c z,
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), canonical_budget_at L S Q N T Z c z⟩,
    canonical_cost_le_budget L S Q N T Z, ?_⟩
  intro ι _ _ e he hB
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  obtain ⟨B⟩ := hB i
  refine ⟨B.chart, B.z, B.z_mem, B.chart_ne, ?_⟩
  calc
    _ ≤ Fintype.card ι * e i := Nat.mul_le_mul_left _
      (canonical_cost_le_budget L S Q N T Z (e i) (he i) B)
    _ = ∑ _j : ι, e i := by simp
    _ ≤ ∑ j, e j := Finset.sum_le_sum fun j _ => hi j (Finset.mem_univ j)
