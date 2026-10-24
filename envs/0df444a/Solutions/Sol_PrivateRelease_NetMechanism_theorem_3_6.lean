-- Prove2me | solution 1 for PrivateRelease.NetMechanism.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T14:25:52.403555+00:00
-- url     : https://prove2.me/submissions/97c55d31-9249-44e7-9577-120a2951f67f

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_Queries

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace FiniteSampling
lemma tail {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : A → ℝ) (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc 0 1)
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | a < |(∑ i, f (ω i)) / n - ∫ x, f x ∂μ|} ≤
      2 * Real.exp (-2 * n * a^2) := by
  let P : Measure (Fin n → A) := Measure.pi (fun _ : Fin n => μ)
  let q : ℝ := ∫ x, f x ∂μ
  have hsub (i : Fin n) :
      HasSubgaussianMGF (fun ω : Fin n → A => f (ω i) - q) (1/4) P := by
    have heq : (∫ ω : Fin n → A, f (ω i) ∂P) = q :=
      integral_comp_eval hf.aestronglyMeasurable
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := P) ((hf.comp (measurable_pi_apply i)).aemeasurable)
      (ae_of_all P (fun ω => hb (ω i)))
    simp only [Function.comp_def] at h
    rw [heq] at h
    convert h using 1 <;> norm_num
  have hind : iIndepFun (fun i : Fin n => fun ω : Fin n → A => f (ω i) - q) P :=
    iIndepFun_pi (fun _ => (hf.sub_const q).aemeasurable)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind
    (s := Finset.univ) (fun i _ => hsub i)
  have hna : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg n) ha
  have hupper := hsum.measure_ge_le hna
  have hlower := hsum.neg.measure_ge_le hna
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hexp : -((n : ℝ) * a)^2 / (2 * (∑ _i : Fin n, (1/4 : ℝ≥0))) =
      -2 * n * a^2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    field_simp
    <;> ring
  rw [hexp] at hupper hlower
  have hinc : {ω : Fin n → A | a < |(∑ i, f (ω i)) / n - q|} ⊆
      {ω | (n : ℝ)*a ≤ ∑ i, (f (ω i)-q)} ∪
      {ω | (n : ℝ)*a ≤ -(∑ i, (f (ω i)-q))} := by
    intro ω h
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum' : (∑ i, (f (ω i)-q)) = (∑ i, f (ω i)) - n*q := by simp [Finset.sum_sub_distrib]
    have hmul : (n : ℝ) * ((∑ i, f (ω i)) / n - q) = (∑ i, f (ω i))-n*q := by field_simp <;> ring
    change a < |(∑ i, f (ω i)) / n - q| at h
    rcases lt_abs.mp h with h | h
    · left
      dsimp
      rw [hsum']
      nlinarith
    · right
      dsimp
      rw [hsum']
      nlinarith
  calc
    _ ≤ P.real ({ω | (n : ℝ)*a ≤ ∑ i, (f (ω i)-q)} ∪
        {ω | (n : ℝ)*a ≤ -(∑ i, (f (ω i)-q))}) := measureReal_mono hinc
    _ ≤ _ := (measureReal_union_le _ _).trans (by
      simp only [Pi.neg_apply] at hlower
      linarith [hupper, hlower])
end FiniteSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace FiniteSampling
lemma exists_sample {A I : Type*} [MeasurableSpace A] [Fintype I]
    (μ : Measure A) [IsProbabilityMeasure μ] (f : I → A → ℝ)
    (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, f i x ∈ Set.Icc 0 1)
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a)
    (hprob : (Fintype.card I : ℝ) * (2 * Real.exp (-2 * n * a^2)) < 1) :
    ∃ ω : Fin n → A, ∀ i, |(∑ j, f i (ω j)) / n - ∫ x, f i x ∂μ| ≤ a := by
  classical
  let P : Measure (Fin n → A) := Measure.pi (fun _ : Fin n => μ)
  by_contra h
  push_neg at h
  have heq : (⋃ i : I, {ω : Fin n → A | a < |(∑ j, f i (ω j)) / n - ∫ x, f i x ∂μ|}) =
      Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact h ω
  have hbad : 1 ≤ (Fintype.card I : ℝ) * (2 * Real.exp (-2 * n * a^2)) := by
    calc
      1 = P.real Set.univ := by simp [P]
      _ = P.real (⋃ i : I, {ω : Fin n → A | a < |(∑ j, f i (ω j)) / n - ∫ x, f i x ∂μ|}) := by rw [heq]
      _ ≤ ∑ i : I, P.real {ω : Fin n → A | a < |(∑ j, f i (ω j)) / n - ∫ x, f i x ∂μ|} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : I, 2 * Real.exp (-2 * n * a^2) :=
        Finset.sum_le_sum (fun i _ => tail μ (f i) (hf i) (hb i) n hn a ha)
      _ = _ := by simp
  exact (not_le_of_gt hprob) hbad
end FiniteSampling

open MeasureTheory ProbabilityTheory PrivateRelease.NetMechanism
open scoped ENNReal BigOperators
namespace FiniteSampling
-- The tuple-count identity follows the helper in vebis's accepted sensitivity proof.
lemma count_input {X : Type} {n : ℕ} (φ : X → Bool) (z : Fin n → X) :
    countQ φ (inputDB z) = (∑ i, if φ (z i) = true then (1 : ℝ) else 0) / n := by
  unfold countQ inputDB
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.sum_boole, Multiset.filter_map, Multiset.card_map]
  rfl
lemma input_get {X : Type} (l : List X) : inputDB l.get = (l : Multiset X) := by
  simp [inputDB, Fin.univ_val_map, List.ofFn_get]
lemma uniform_mean {X : Type} (l : List X) (hn : 0 < l.length) (φ : X → Bool) :
    letI : Nonempty (Fin l.length) := ⟨⟨0,hn⟩⟩
    (∫ i : Fin l.length, (if φ (l.get i) = true then (1 : ℝ) else 0)
      ∂(PMF.uniformOfFintype (Fin l.length)).toMeasure) = countQ φ (l : Multiset X) := by
  letI : Nonempty (Fin l.length) := ⟨⟨0,hn⟩⟩
  rw [← input_get l, count_input, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring
lemma size_bound (c : ℕ) (hc : 3 ≤ c) (a : ℝ) (ha : 0 < a) :
    0 < ⌈Real.log (c : ℝ) / a^2⌉₊ ∧
      (c : ℝ) * (2 * Real.exp (-2 * (⌈Real.log (c : ℝ) / a^2⌉₊ : ℕ) * a^2)) < 1 := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hc3 : (3 : ℝ) ≤ c := by exact_mod_cast hc
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hlog : 0 < Real.log (c : ℝ) := Real.log_pos (by linarith)
  refine ⟨Nat.ceil_pos.mpr (div_pos hlog ha2), ?_⟩
  have hceil := Nat.le_ceil (Real.log (c : ℝ) / a^2)
  have hmul : Real.log (c : ℝ) ≤ (⌈Real.log (c : ℝ) / a^2⌉₊ : ℕ) * a^2 :=
    (div_le_iff₀ ha2).mp hceil
  have he : Real.exp (-2 * (⌈Real.log (c : ℝ) / a^2⌉₊ : ℕ) * a^2) ≤
      1 / ((c : ℝ) * c) := by
    calc
      _ ≤ Real.exp (- (Real.log (c : ℝ) + Real.log (c : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_add, Real.exp_log hcpos]; simp [one_div]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hcpos
  calc
    _ ≤ (c : ℝ) * (2 * (1 / ((c : ℝ)*c))) := by gcongr
    _ = 2 / (c : ℝ) := by field_simp <;> ring
    _ < 1 := (div_lt_one hcpos).mpr (by linarith)
end FiniteSampling

open MeasureTheory PrivateRelease.NetMechanism

theorem sampling_lemma {X : Type} (C : Finset (X → Bool)) (α : ℝ) (hC : 3 ≤ C.card) (hα : 0 < α)
    (D : Database X) :
    ∃ D' : Database X, Multiset.card D'.1 = ⌈Real.log (C.card : ℝ) / α ^ 2⌉₊ ∧
      ∀ φ ∈ C, |countQ φ D.1 - countQ φ D'.1| ≤ α := by
  classical
  let l := D.1.toList
  have hl : 0 < l.length := by
    simpa [l] using Multiset.card_pos.mpr D.2
  letI : Nonempty (Fin l.length) := ⟨⟨0,hl⟩⟩
  let n := ⌈Real.log (C.card : ℝ) / α^2⌉₊
  have hn := (FiniteSampling.size_bound C.card hC α hα).1
  let μ := (PMF.uniformOfFintype (Fin l.length)).toMeasure
  let f : C → Fin l.length → ℝ := fun φ i => if φ.1 (l.get i) = true then 1 else 0
  obtain ⟨ω,hω⟩ := FiniteSampling.exists_sample μ f
    (fun _ => measurable_of_countable _) (fun φ i => by dsimp [f]; split_ifs <;> simp)
    n hn α hα.le (by simpa using (FiniteSampling.size_bound C.card hC α hα).2)
  let z : Fin n → X := fun j => l.get (ω j)
  have hz : inputDB z ≠ 0 := by
    intro h
    have hc := congrArg Multiset.card h
    simp [inputDB] at hc
    omega
  refine ⟨⟨inputDB z,hz⟩, by simp [inputDB,n], ?_⟩
  intro φ hφ
  have he := hω ⟨φ,hφ⟩
  have hmean : (∫ i : Fin l.length, f ⟨φ,hφ⟩ i ∂μ) = countQ φ D.1 := by
    simpa [f,μ,l] using FiniteSampling.uniform_mean l hl φ
  rw [hmean] at he
  rw [FiniteSampling.count_input]
  simpa [f,z,abs_sub_comm] using he

open PrivateRelease.NetMechanism
namespace FiniteSampling
lemma exists_tuple {X : Type} {n : ℕ} (D : Multiset X) (h : D.card = n) :
    ∃ z : Fin n → X, inputDB z = D := by
  have hh : ∃ z : Fin D.toList.length → X, inputDB z = D :=
    ⟨D.toList.get, by simpa using input_get D.toList⟩
  have hlen : D.toList.length = n := (Multiset.length_toList D).trans h
  exact hlen ▸ hh

lemma bounded_net {X : Type} [Fintype X] (C : Finset (X → Bool)) (α : ℝ)
    (hC : 3 ≤ C.card) (hα : 0 < α) :
    ∃ N : Finset (Database X), IsNet (countingClass (C : Set (X → Bool))) α N ∧
      N.card ≤ Fintype.card X ^ ⌈Real.log (C.card : ℝ) / α^2⌉₊ := by
  classical
  let n := ⌈Real.log (C.card : ℝ) / α^2⌉₊
  have hn : 0 < n := (size_bound C.card hC α hα).1
  have hne (z : Fin n → X) : inputDB z ≠ 0 := by
    intro h
    have hc := congrArg Multiset.card h
    simp [inputDB] at hc
    omega
  let F : (Fin n → X) → Database X := fun z => ⟨inputDB z,hne z⟩
  refine ⟨Finset.univ.image F, ?_, ?_⟩
  · intro D
    obtain ⟨D',hcard,happrox⟩ := sampling_lemma C α hC hα D
    obtain ⟨z,hz⟩ := exists_tuple D'.1 hcard
    refine ⟨F z,Finset.mem_image.mpr ⟨z,Finset.mem_univ z,rfl⟩,?_⟩
    intro Q hQ
    obtain ⟨φ,hφ,rfl⟩ := hQ
    change |countQ φ D.1 - countQ φ (inputDB z)| ≤ α
    rw [hz]
    exact happrox φ hφ
  · calc
      _ ≤ (Finset.univ : Finset (Fin n → X)).card := Finset.card_image_le
      _ = _ := by simp [n]
end FiniteSampling

theorem solution {X : Type} [Fintype X] (C : Finset (X → Bool)) (α : ℝ)
    (hC : 3 ≤ C.card) (hα : 0 < α) :
    (∃ N : Finset (Database X), IsMinNet (countingClass (C : Set (X → Bool))) α N) ∧
      ∀ N : Finset (Database X), IsMinNet (countingClass (C : Set (X → Bool))) α N →
        N.card ≤ Fintype.card X ^ ⌈Real.log (C.card : ℝ) / α^2⌉₊ := by
  classical
  obtain ⟨N₀,hnet,hbound⟩ := FiniteSampling.bounded_net C α hC hα
  have hex : ∃ k : ℕ, ∃ N : Finset (Database X),
      IsNet (countingClass (C : Set (X → Bool))) α N ∧ N.card = k :=
    ⟨N₀.card,N₀,hnet,rfl⟩
  obtain ⟨N,hN,hcard⟩ := Nat.find_spec hex
  constructor
  · refine ⟨N,hN,?_⟩
    intro N' hN'
    rw [hcard]
    exact Nat.find_le ⟨N',hN',rfl⟩
  · intro N' hN'
    exact (hN'.2 N₀ hnet).trans hbound
#print axioms solution
