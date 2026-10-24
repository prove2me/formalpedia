-- Prove2me | solution 1 for PrivateRelease.NetMechanism.corollary_3_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T13:20:34.44168+00:00
-- url     : https://prove2.me/submissions/9b150842-6255-467e-87e6-b9ceadd70dc2

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_ExpMech
/-
Corollary 3.5 of Blum, Ligett and Roth (arXiv:1109.2229v1, p.9).
Reuses campaign Property 3.4, submission 24e5857c-8c62-4668-b656-02013403cdce,
and vebis counting-query sensitivity, submission bf2728dc-7c0f-4f91-8ec9-33f477179fcb.
Original accepted proof bodies retained with final declarations renamed.
OpenAI Codex supplied the zero-sensitivity argument for Alexander Richard Towell.
No novelty or independent human review is claimed.
-/

open MeasureTheory PrivateRelease.NetMechanism
namespace ExponentialPrivacy

lemma sensitivity {X O : Type} [Fintype X] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (z z' : Fin n → X)
    (hz : PrivLearn.Generic.Neighbors z z') (r : O) (hr : r ∈ R) :
    |q z r - q z' r| ≤ scoreSens R q := by
  classical
  have h1 : |q z r - q z' r| ≤ GS (fun t => q t r) := by
    unfold GS
    exact le_ciSup (f := fun t : {t : (Fin n → X) × (Fin n → X) // PrivLearn.Generic.Neighbors t.1 t.2} => |q t.1.1 r - q t.1.2 r|) (Set.finite_range _).bddAbove ⟨(z,z'),hz⟩
  have h2 : GS (fun t => q t r) ≤ scoreSens R q := by
    unfold scoreSens
    exact le_ciSup (f := fun t : R => GS (fun z => q z t.1)) (Set.finite_range _).bddAbove ⟨r,hr⟩
  exact h1.trans h2

lemma neighbors_symm {X : Type} {n : ℕ} {z z' : Fin n → X}
    (h : PrivLearn.Generic.Neighbors z z') : PrivLearn.Generic.Neighbors z' z := by
  obtain ⟨i,hi,hrest⟩ := h
  exact ⟨i,Ne.symm hi,fun j hj => (hrest j hj).symm⟩

noncomputable def weight {X O : Type} {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (z : Fin n → X) (r : O) : ℝ :=
  Real.exp (ε * q z r / (2 * scoreSens R q))

noncomputable def normConst {X O : Type} {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (z : Fin n → X) : ℝ :=
  ∑ r ∈ R, weight R q ε z r

lemma norm_pos {X O : Type} {n : ℕ} (R : Finset O) (q : (Fin n → X) → O → ℝ)
    (ε : ℝ) (z : Fin n → X) (hR : R.Nonempty) : 0 < normConst R q ε z := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hR

lemma weight_bound {X O : Type} [Fintype X] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hq : 0 < scoreSens R q) (hε : 0 < ε)
    (z z' : Fin n → X) (hz : PrivLearn.Generic.Neighbors z z') (r : O) (hr : r ∈ R) :
    weight R q ε z r ≤ Real.exp (ε/2) * weight R q ε z' r := by
  have hdiff := (le_abs_self (q z r-q z' r)).trans (sensitivity R q z z' hz r hr)
  have hscaled := mul_le_mul_of_nonneg_left hdiff hε.le
  have he : ε*q z r/(2*scoreSens R q) ≤ ε/2+ε*q z' r/(2*scoreSens R q) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*scoreSens R q)).mpr
    have hcancel : (ε/2+ε*q z' r/(2*scoreSens R q))*(2*scoreSens R q) =
        ε*scoreSens R q+ε*q z' r := by field_simp <;> ring
    rw [hcancel]; linarith
  simpa only [weight, Real.exp_add] using Real.exp_le_exp.mpr he

lemma probability_bound {X O : Type} [Fintype X] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hR : R.Nonempty)
    (hq : 0 < scoreSens R q) (hε : 0 < ε)
    (z z' : Fin n → X) (hz : PrivLearn.Generic.Neighbors z z') (r : O) (hr : r ∈ R) :
    weight R q ε z r / normConst R q ε z ≤
      Real.exp ε * (weight R q ε z' r / normConst R q ε z') := by
  have hZ := norm_pos R q ε z hR
  have hZ' := norm_pos R q ε z' hR
  have hw := weight_bound R q ε hq hε z z' hz r hr
  have hn : normConst R q ε z' ≤ Real.exp (ε/2) * normConst R q ε z := by
    unfold normConst
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => weight_bound R q ε hq hε z' z (neighbors_symm hz) j hj)
  have hmul1 := mul_le_mul_of_nonneg_right hw hZ'.le
  have hmul2 := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ Real.exp (ε/2) * weight R q ε z' r by unfold weight; positivity)
  have he : Real.exp (ε/2)*Real.exp (ε/2)=Real.exp ε := by
    rw [← Real.exp_add]; congr 1; ring
  have hp : weight R q ε z r * normConst R q ε z' ≤
      (Real.exp ε * weight R q ε z' r) * normConst R q ε z := by
    calc _ ≤ (Real.exp (ε/2) * weight R q ε z' r) * normConst R q ε z' := hmul1
      _ ≤ (Real.exp (ε/2) * weight R q ε z' r) *
          (Real.exp (ε/2) * normConst R q ε z) := hmul2
      _ = _ := by rw [show (Real.exp (ε/2) * weight R q ε z' r) *
          (Real.exp (ε/2) * normConst R q ε z) =
          (Real.exp (ε/2)*Real.exp (ε/2))*weight R q ε z' r*normConst R q ε z by ring,he]
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ hZ hZ').mpr hp

lemma normalized {X O : Type} [MeasurableSpace O] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hR : R.Nonempty) (z : Fin n → X) :
    IsProbabilityMeasure (expMech R q ε z) := by
  classical
  have hZ := norm_pos R q ε z hR
  have hn : ∑ r ∈ R, weight R q ε z r / normConst R q ε z = 1 := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hZ)
  constructor
  simp only [expMech, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  change (∑ r ∈ R, ENNReal.ofReal (weight R q ε z r / normConst R q ε z)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (s := R) (f := fun r => weight R q ε z r / normConst R q ε z) (fun r _ => by unfold weight; positivity),hn]
  exact ENNReal.ofReal_one

end ExponentialPrivacy

theorem exponential_mechanism {X O : Type} [Fintype X] [MeasurableSpace O] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hR : R.Nonempty) (hq : 0 < scoreSens R q)
    (hε : 0 < ε) :
    PrivLearn.Generic.IsDP (expMech R q ε) ε ∧
      ∀ z : Fin n → X, IsProbabilityMeasure (expMech R q ε z) := by
  classical
  constructor
  · intro z z' hz S hS
    unfold expMech
    rw [Measure.finsetSum_apply,Measure.finsetSum_apply,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    rw [Measure.smul_apply,Measure.smul_apply]
    change ENNReal.ofReal (ExponentialPrivacy.weight R q ε z r / ExponentialPrivacy.normConst R q ε z) *
      Measure.dirac r S ≤ ENNReal.ofReal (Real.exp ε) *
      (ENNReal.ofReal (ExponentialPrivacy.weight R q ε z' r / ExponentialPrivacy.normConst R q ε z') * Measure.dirac r S)
    rw [← mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos ε).le]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (ExponentialPrivacy.probability_bound R q ε hR hq hε z z' hz r hr)) zero_le
  · exact ExponentialPrivacy.normalized R q ε hR

#print axioms exponential_mechanism

open PrivateRelease.NetMechanism
namespace NetUtilitySupport

lemma query_difference {X : Type} [Fintype X] {n : ℕ}
    (f : (Fin n → X) → ℝ) (z z' : Fin n → X)
    (hz : PrivLearn.Generic.Neighbors z z') : |f z - f z'| ≤ GS f := by
  classical
  unfold GS
  exact le_ciSup (f := fun t : {t : (Fin n → X) × (Fin n → X) // PrivLearn.Generic.Neighbors t.1 t.2} =>
    |f t.1.1 - f t.1.2|) (Set.finite_range _).bddAbove ⟨(z,z'),hz⟩

lemma net_error_le {X : Type} [Fintype X] {n : ℕ}
    (QC : Set (Multiset X → ℝ)) [Nonempty QC] (Δ : ℝ)
    (hΔ : ∀ Q ∈ QC, GS (fun z : Fin n → X => Q (inputDB z)) ≤ Δ)
    (z z' : Fin n → X) (hz : PrivLearn.Generic.Neighbors z z') (D : Database X)
    (hbdd : BddAbove (Set.range fun Q : QC => |Q.1 (inputDB z') - Q.1 D.1|)) :
    (⨆ Q : QC, |Q.1 (inputDB z) - Q.1 D.1|) ≤
      (⨆ Q : QC, |Q.1 (inputDB z') - Q.1 D.1|) + Δ := by
  apply ciSup_le
  intro Q
  have hq := (query_difference (fun z => Q.1 (inputDB z)) z z' hz).trans (hΔ Q.1 Q.2)
  have hu := le_ciSup (f := fun Q : QC => |Q.1 (inputDB z') - Q.1 D.1|) hbdd Q
  have ht := abs_sub_le (Q.1 (inputDB z)) (Q.1 (inputDB z')) (Q.1 D.1)
  linarith

lemma net_score_difference {X : Type} [Fintype X] {n : ℕ}
    (QC : Set (Multiset X → ℝ)) [Nonempty QC] (Δ : ℝ)
    (hΔ : ∀ Q ∈ QC, GS (fun z : Fin n → X => Q (inputDB z)) ≤ Δ)
    (z z' : Fin n → X) (hz : PrivLearn.Generic.Neighbors z z') (D : Database X)
    (hbdd : BddAbove (Set.range fun Q : QC => |Q.1 (inputDB z) - Q.1 D.1|))
    (hbdd' : BddAbove (Set.range fun Q : QC => |Q.1 (inputDB z') - Q.1 D.1|)) :
    |netScore QC z D - netScore QC z' D| ≤ Δ := by
  have hf := net_error_le QC Δ hΔ z z' hz D hbdd'
  have hr := net_error_le QC Δ hΔ z' z (ExponentialPrivacy.neighbors_symm hz) D hbdd
  unfold netScore
  rw [abs_le]
  constructor <;> linarith

lemma net_sensitivity_le {X : Type} [Fintype X] {n : ℕ}
    (QC : Set (Multiset X → ℝ)) [Nonempty QC] (Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (N : Finset (Database X)) (hN : N.Nonempty)
    (hΔ : ∀ Q ∈ QC, GS (fun z : Fin n → X => Q (inputDB z)) ≤ Δ)
    (hbdd : ∀ z : Fin n → X, ∀ D ∈ N,
      BddAbove (Set.range fun Q : QC => |Q.1 (inputDB z) - Q.1 D.1|)) :
    netSens n QC N ≤ Δ := by
  classical
  have hinner (D : Database X) (hD : D ∈ N) : GS (fun z : Fin n → X => netScore QC z D) ≤ Δ := by
    unfold GS
    let T := {t : (Fin n → X) × (Fin n → X) // PrivLearn.Generic.Neighbors t.1 t.2}
    by_cases ht : Nonempty T
    · letI := ht
      exact ciSup_le (fun t : T => net_score_difference QC Δ hΔ t.1.1 t.1.2 t.2 D
        (hbdd t.1.1 D hD) (hbdd t.1.2 D hD))
    · letI : IsEmpty T := not_nonempty_iff.mp ht
      change (⨆ t : T, |netScore QC t.1.1 D - netScore QC t.1.2 D|) ≤ Δ
      simpa using hΔ0
  letI : Nonempty N := hN.to_subtype
  exact ciSup_le (fun D : N => hinner D.1 D.2)

#print axioms net_sensitivity_le

lemma pointwise_tail_bound {X O : Type} {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε g b : ℝ)
    (hq : 0 < scoreSens R q) (hε : 0 < ε) (z : Fin n → X)
    (hbest : ∃ r₀ ∈ R, g ≤ q z r₀) (r : O) (hr : q z r ≤ b) :
    ExponentialPrivacy.weight R q ε z r / ExponentialPrivacy.normConst R q ε z ≤
      Real.exp (ε * (b-g) / (2*scoreSens R q)) := by
  classical
  obtain ⟨r₀,hr₀,hg⟩ := hbest
  have hR : R.Nonempty := ⟨r₀,hr₀⟩
  have hZ := ExponentialPrivacy.norm_pos R q ε z hR
  have hscale : 0 ≤ ε / (2*scoreSens R q) := by positivity
  have hmono (a b : ℝ) (hab : a ≤ b) :
      Real.exp (ε*a/(2*scoreSens R q)) ≤ Real.exp (ε*b/(2*scoreSens R q)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab hε.le) (by positivity)
  have hgZ : Real.exp (ε*g/(2*scoreSens R q)) ≤ ExponentialPrivacy.normConst R q ε z := by
    calc _ ≤ ExponentialPrivacy.weight R q ε z r₀ := hmono g (q z r₀) hg
      _ ≤ _ := by
        unfold ExponentialPrivacy.normConst
        exact Finset.single_le_sum (fun (j : O) (_ : j ∈ R) =>
          show 0 ≤ ExponentialPrivacy.weight R q ε z j from (Real.exp_pos _).le) hr₀
  calc
    _ ≤ Real.exp (ε*b/(2*scoreSens R q)) / ExponentialPrivacy.normConst R q ε z :=
      (div_le_div_iff_of_pos_right hZ).mpr (hmono (q z r) b hr)
    _ ≤ Real.exp (ε*b/(2*scoreSens R q)) / Real.exp (ε*g/(2*scoreSens R q)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hgZ
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

lemma finite_tail_bound {X O : Type} {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε g b : ℝ)
    (hq : 0 < scoreSens R q) (hε : 0 < ε) (z : Fin n → X)
    (hbest : ∃ r₀ ∈ R, g ≤ q z r₀) :
    ∑ r ∈ R, (if q z r ≤ b then
      ExponentialPrivacy.weight R q ε z r / ExponentialPrivacy.normConst R q ε z else 0) ≤
      (R.card : ℝ) * Real.exp (ε * (b-g) / (2*scoreSens R q)) := by
  classical
  calc
    _ ≤ ∑ r ∈ R, Real.exp (ε * (b-g) / (2*scoreSens R q)) := by
      apply Finset.sum_le_sum
      intro r hr
      split_ifs with hh
      · exact pointwise_tail_bound R q ε g b hq hε z hbest r hh
      · exact (Real.exp_pos _).le
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

#print axioms finite_tail_bound
end NetUtilitySupport

open MeasureTheory PrivateRelease.NetMechanism ExponentialPrivacy NetUtilitySupport
namespace NetUtility

lemma query_nonempty {X : Type} {n : ℕ} (QC : Set (Multiset X → ℝ))
    (N : Finset (Database X)) (hsens : 0 < netSens n QC N) : Nonempty QC := by
  by_contra h
  letI : IsEmpty QC := not_nonempty_iff.mp h
  simp [netSens, scoreSens, netScore, GS] at hsens

lemma net_nonempty {X : Type} {n : ℕ} (QC : Set (Multiset X → ℝ))
    (N : Finset (Database X)) (hsens : 0 < netSens n QC N) : N.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  subst N
  simpa [netSens, scoreSens] using hsens

lemma gs_nonneg {X : Type} {n : ℕ} (f : (Fin n → X) → ℝ) : 0 ≤ GS f := by
  exact Real.iSup_nonneg (fun _ => abs_nonneg _)

lemma input_nonempty {X : Type} {n : ℕ} (hn : 1 ≤ n) (z : Fin n → X) : inputDB z ≠ 0 := by
  intro h
  have hc := congrArg Multiset.card h
  simp [inputDB] at hc
  omega

lemma numerical_tail (c ε α δ Δ s : ℝ) (hc : 1 ≤ c)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) (hsΔ : s ≤ Δ)
    (hα : 2 * Δ / ε * Real.log (c / δ) ≤ α) :
    c * Real.exp (ε * (-α) / (2*s)) ≤ δ := by
  have hΔ : 0 < Δ := hs.trans_le hsΔ
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hratio : 1 ≤ c / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hlog : 0 ≤ Real.log (c/δ) := Real.log_nonneg hratio
  have hal : 2*Δ*Real.log (c/δ) ≤ α*ε := by
    apply (div_le_iff₀ hε).mp
    simpa only [div_mul_eq_mul_div] using hα
  have hsl : 2*s*Real.log (c/δ) ≤ α*ε := by
    calc _ ≤ 2*Δ*Real.log (c/δ) := mul_le_mul_of_nonneg_right (by linarith) hlog
      _ ≤ _ := hal
  have he : ε*(-α)/(2*s) ≤ -Real.log (c/δ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*s)).mpr
    nlinarith
  calc
    _ ≤ c * Real.exp (-Real.log (c/δ)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hc0.le
    _ = δ := by rw [Real.exp_neg, Real.exp_log (div_pos hc0 hδ)]; field_simp

lemma event_mass {X O : Type} [MeasurableSpace O] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (z : Fin n → X) (S : Set O) [DecidablePred (· ∈ S)]
    (hS : MeasurableSet S) :
    expMech R q ε z S = ENNReal.ofReal (∑ r ∈ R,
      if r ∈ S then weight R q ε z r / normConst R q ε z else 0) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => by
    split_ifs
    · exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le))
    · exact le_rfl)]
  unfold expMech
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Measure.smul_apply, Measure.dirac_apply' r hS]
  by_cases h : r ∈ S <;> simp [h,weight,normConst]

#print axioms query_nonempty
#print axioms numerical_tail
#print axioms event_mass
end NetUtility

open MeasureTheory PrivateRelease.NetMechanism ExponentialPrivacy NetUtilitySupport NetUtility

 theorem property_3_4 {X : Type} [Fintype X] {n : ℕ} (hn : 1 ≤ n) (QC : Set (Multiset X → ℝ))
    (ε α δ Δ : ℝ) (N : Finset (Database X)) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : IsMinNet QC α N) (hsens : 0 < netSens n QC N)
    (hΔ : ∀ Q ∈ QC, GS (fun z : Fin n → X => Q (inputDB z)) ≤ Δ)
    (hbdd : ∀ (z : Fin n → X), ∀ D' ∈ N,
      BddAbove (Set.range fun Q : QC => |Q.1 (inputDB z) - Q.1 D'.1|))
    (hα : 2 * Δ / ε * Real.log ((N.card : ℝ) / δ) ≤ α) :
    Useful QC (2 * α) δ (netMech (n := n) QC ε N) := by
  classical
  letI : Nonempty QC := query_nonempty QC N hsens
  have hNne := net_nonempty QC N hsens
  obtain ⟨Q⟩ := ‹Nonempty QC›
  have hΔ0 : 0 ≤ Δ := (gs_nonneg (fun z : Fin n → X => Q.1 (inputDB z))).trans (hΔ Q.1 Q.2)
  have hbound := net_sensitivity_le QC Δ hΔ0 N hNne hΔ hbdd
  intro z
  obtain ⟨r₀,hr₀,hgood⟩ := hN.1 ⟨inputDB z, input_nonempty hn z⟩
  have hbest : ∃ r₀ ∈ N, -α ≤ netScore QC z r₀ := by
    refine ⟨r₀,hr₀,?_⟩
    change -α ≤ -(⨆ Q : QC, |Q.1 (inputDB z) - Q.1 r₀.1|)
    exact neg_le_neg (ciSup_le (fun Q : QC => hgood Q.1 Q.2))
  let G : Set (Database X) := {D | ∀ Q ∈ QC, |Q D.1 - Q (inputDB z)| ≤ 2*α}
  let p : Database X → ℝ := fun r => weight N (netScore QC) ε z r / normConst N (netScore QC) ε z
  have hp (r : Database X) : 0 ≤ p r := by
    exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le))
  have htotal : ∑ r ∈ N, p r = 1 := by
    dsimp [p]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (norm_pos N (netScore QC) ε z hNne))
  have hbadscore (r : Database X) (hr : r ∈ N) (hbad : r ∉ G) : netScore QC z r ≤ -(2*α) := by
    change ¬ (∀ Q ∈ QC, |Q r.1 - Q (inputDB z)| ≤ 2*α) at hbad
    push_neg at hbad
    obtain ⟨Q,hQ,herr⟩ := hbad
    have hu := le_ciSup (f := fun Q : QC => |Q.1 (inputDB z) - Q.1 r.1|) (hbdd z r hr) ⟨Q,hQ⟩
    have hh : 2*α < |Q (inputDB z) - Q r.1| := by simpa [abs_sub_comm] using herr
    exact neg_le_neg (hh.le.trans hu)
  have hbad : (∑ r ∈ N, if r ∈ G then 0 else p r) ≤ δ := by
    calc
      _ ≤ (N.card : ℝ) * Real.exp (ε * (-α) / (2*netSens n QC N)) := by
        calc _ ≤ ∑ r ∈ N, Real.exp (ε * (-α) / (2*netSens n QC N)) := by
               apply Finset.sum_le_sum
               intro r hr
               split_ifs with hG
               · exact (Real.exp_pos _).le
               · have h := pointwise_tail_bound N (netScore QC) ε (-α) (-(2*α)) hsens hε z hbest r (hbadscore r hr hG)
                 convert h using 1 <;> congr 2 <;> ring
          _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ δ := numerical_tail (N.card : ℝ) ε α δ Δ (netSens n QC N)
        (by exact_mod_cast Nat.succ_le_of_lt hNne.card_pos) hε hδ hδ1 hsens hbound hα
  have hsplit : (∑ r ∈ N, if r ∈ G then p r else 0) +
      (∑ r ∈ N, if r ∈ G then 0 else p r) = 1 := by
    rw [← Finset.sum_add_distrib,← htotal]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> simp
  have hgoodmass : 1-δ ≤ ∑ r ∈ N, if r ∈ G then p r else 0 := by linarith
  change ENNReal.ofReal (1-δ) ≤ expMech N (netScore QC) ε z G
  rw [event_mass N (netScore QC) ε z G (by trivial)]
  exact ENNReal.ofReal_le_ofReal hgoodmass

#print axioms property_3_4


set_option autoImplicit false
open PrivateRelease.NetMechanism

theorem counting_sensitivity {X : Type} (φ : X → Bool) (n : ℕ) (hn : 1 ≤ n) :
    GS (fun z : Fin n → X => countQ φ (inputDB z)) ≤ 1 / (n : ℝ) := by
  have key : ∀ z : Fin n → X, countQ φ (inputDB z) =
      (∑ i, if φ (z i) = true then (1 : ℝ) else 0) / n := by
    intro z
    unfold countQ inputDB
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Finset.sum_boole, Multiset.filter_map, Multiset.card_map]
    rfl
  unfold GS
  have hn0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  refine Real.iSup_le (fun p => ?_) hn0
  obtain ⟨i, hi, hj⟩ := p.2
  show |countQ φ (inputDB p.1.1) - countQ φ (inputDB p.1.2)| ≤ 1 / (n : ℝ)
  rw [key, key, ← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · split_ifs <;> simp
  · intro j _ hji
    rw [hj j hji]; simp
  · intro h; exact absurd (Finset.mem_univ i) h

open MeasureTheory PrivateRelease.NetMechanism ExponentialPrivacy NetUtilitySupport NetUtility
namespace CountingUtility

lemma score_const {X O : Type} [Fintype X] {n : ℕ}
    (R : Finset O) (q : (Fin n → X) → O → ℝ) (hs : scoreSens R q = 0)
    (r : O) (hr : r ∈ R) (z z' : Fin n → X) : q z r = q z' r := by
  classical
  have step (a b : Fin n → X) (h : PrivLearn.Generic.Neighbors a b) : q a r = q b r := by
    have hle := sensitivity R q a b h r hr
    rw [hs] at hle
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)
  have general : ∀ S : Finset (Fin n), ∀ a b : Fin n → X,
      (∀ i, i ∉ S → a i = b i) → q a r = q b r := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro a b h
      congr 1
      funext i
      exact h i (by simp)
    | @insert i S hi ih =>
      intro a b h
      let u := Function.update a i (b i)
      have hstep : q a r = q u r := by
        by_cases he : a i = b i
        · have hu : u = a := by
            funext j
            by_cases hj : j = i <;> simp [u, hj, he]
          rw [hu]
        · apply step
          refine ⟨i, ?_, ?_⟩
          · simpa [u] using he
          · intro j hj
            simp [u, hj]
      exact hstep.trans (ih u b (by
        intro j hj
        by_cases hji : j = i
        · simp [u,hji]
        · simpa [u,hji] using h j (by simp [hj,hji])))
  exact general Finset.univ z z' (by simp)

lemma count_range {X : Type} (φ : X → Bool) (D : Multiset X) :
    0 ≤ countQ φ D ∧ countQ φ D ≤ 1 := by
  constructor
  · unfold countQ; positivity
  · unfold countQ
    apply div_le_one_of_le₀
    · exact_mod_cast Multiset.card_le_card (Multiset.filter_le (fun x => φ x = true) D)
    · positivity

lemma query_range {X : Type} (C : Set (X → Bool)) (Q : Multiset X → ℝ)
    (hQ : Q ∈ countingClass C) (D : Multiset X) : 0 ≤ Q D ∧ Q D ≤ 1 := by
  obtain ⟨φ,hφ,rfl⟩ := hQ
  exact count_range φ D

lemma error_le_one {X : Type} (C : Set (X → Bool)) (Q : Multiset X → ℝ)
    (hQ : Q ∈ countingClass C) (D E : Multiset X) : |Q D-Q E| ≤ 1 := by
  obtain ⟨hD,hD'⟩ := query_range C Q hQ D
  obtain ⟨hE,hE'⟩ := query_range C Q hQ E
  rw [abs_le]; constructor <;> linarith

lemma error_bdd {X : Type} (C : Set (X → Bool)) (D E : Multiset X) :
    BddAbove (Set.range fun Q : countingClass C => |Q.1 D - Q.1 E|) := by
  refine ⟨1,?_⟩
  rintro _ ⟨Q,rfl⟩
  exact error_le_one C Q.1 Q.2 D E

lemma count_constant {X : Type} {n : ℕ} (hn : 1 ≤ n) (φ : X → Bool) (x : X) :
    countQ φ (inputDB (fun _ : Fin n => x)) = if φ x = true then 1 else 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have key : ∀ z : Fin n → X, countQ φ (inputDB z) =
      (∑ i, if φ (z i) = true then (1 : ℝ) else 0) / n := by
    intro z
    unfold countQ inputDB
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Finset.sum_boole, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [key]
  by_cases h : φ x = true
  · simp [h,hn0]
  · simp [h]

lemma count_of_constant {X : Type} (φ : X → Bool) (b : Bool) (h : ∀ x, φ x = b)
    (D : Multiset X) (hD : D ≠ 0) : countQ φ D = if b = true then 1 else 0 := by
  have hc : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast (show D.card ≠ 0 from fun h => hD (Multiset.card_eq_zero.mp h))
  cases b <;> simp [countQ,h,hc]

lemma zero_sensitivity_accuracy {X : Type} [Fintype X] {n : ℕ} (hn : 1 ≤ n)
    (C : Set (X → Bool)) (α : ℝ) (N : Finset (Database X))
    (hN : IsNet (countingClass C) α N) (hs : netSens n (countingClass C) N = 0)
    (z : Fin n → X) (D : Database X) :
    ∀ Q ∈ countingClass C, |Q D.1 - Q (inputDB z)| ≤ 2*α := by
  classical
  intro Q hQ
  letI : Nonempty (countingClass C) := ⟨⟨Q,hQ⟩⟩
  obtain ⟨r,hr,hgood⟩ := hN ⟨inputDB z,input_nonempty hn z⟩
  have ha : 0 ≤ α := (abs_nonneg _).trans (hgood Q hQ)
  by_cases hbig : 1 ≤ 2*α
  · exact (error_le_one C Q hQ D.1 (inputDB z)).trans hbig
  have hbase : -α ≤ netScore (countingClass C) z r := by
    exact neg_le_neg (ciSup_le (fun T : countingClass C => hgood T.1 T.2))
  have herr (x : X) : |Q (inputDB (fun _ : Fin n => x))-Q r.1| ≤ α := by
    have he := score_const N (netScore (countingClass C)) hs r hr z (fun _ => x)
    rw [he] at hbase
    have hle := le_ciSup (f := fun T : countingClass C =>
      |T.1 (inputDB (fun _ : Fin n => x))-T.1 r.1|)
      (error_bdd C (inputDB (fun _ : Fin n => x)) r.1) ⟨Q,hQ⟩
    unfold netScore at hbase
    linarith
  obtain ⟨φ,hφ,rfl⟩ := hQ
  let x₀ := z ⟨0,by omega⟩
  have hconst : ∀ x, φ x = φ x₀ := by
    intro x
    have hx := herr x
    have h0 := herr x₀
    rw [count_constant hn φ x] at hx
    rw [count_constant hn φ x₀] at h0
    have hx' := abs_le.mp hx
    have h0' := abs_le.mp h0
    cases hxv : φ x <;> cases h0v : φ x₀ <;> simp_all <;> linarith
  rw [count_of_constant φ (φ x₀) hconst D.1 D.2,
      count_of_constant φ (φ x₀) hconst (inputDB z) (input_nonempty hn z)]
  simpa using (show 0 ≤ 2*α by linarith)

end CountingUtility

open MeasureTheory PrivateRelease.NetMechanism ExponentialPrivacy NetUtilitySupport NetUtility CountingUtility

theorem solution {X : Type} [Fintype X] {n : ℕ} (hn : 1 ≤ n) (C : Set (X → Bool))
    (ε α δ : ℝ) (N : Finset (Database X)) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : IsMinNet (countingClass C) α N)
    (hα : 2 / (ε * n) * Real.log ((N.card : ℝ) / δ) ≤ α) :
    Useful (countingClass C) (2 * α) δ (netMech (n := n) (countingClass C) ε N) := by
  classical
  by_cases hs : 0 < netSens n (countingClass C) N
  · apply property_3_4 hn (countingClass C) ε α δ (1/(n:ℝ)) N hε hδ hδ1 hN hs
    · rintro _ ⟨φ,hφ,rfl⟩
      exact counting_sensitivity φ n hn
    · intro z D hD
      exact error_bdd C (inputDB z) D.1
    · convert hα using 1 <;> congr 1 <;> ring
  · have hz : netSens n (countingClass C) N = 0 := by
      apply le_antisymm (le_of_not_gt hs)
      exact Real.iSup_nonneg (fun r => gs_nonneg _)
    intro z
    obtain ⟨r,hr,hgood⟩ := hN.1 ⟨inputDB z,input_nonempty hn z⟩
    have hNne : N.Nonempty := ⟨r,hr⟩
    let G : Set (Database X) := {D | ∀ Q ∈ countingClass C, |Q D.1-Q (inputDB z)| ≤ 2*α}
    have hG : G = Set.univ := by
      ext D
      simp only [Set.mem_univ, iff_true]
      exact zero_sensitivity_accuracy hn C α N hN.1 hz z D
    change ENNReal.ofReal (1-δ) ≤ expMech N (netScore (countingClass C)) ε z G
    rw [hG]
    letI := normalized N (netScore (countingClass C)) ε hNne z
    rw [measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by linarith)

#print axioms solution
