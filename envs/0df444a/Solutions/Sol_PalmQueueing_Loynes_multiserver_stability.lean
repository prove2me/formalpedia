-- Prove2me | solution 1 for PalmQueueing.Loynes.multiserver_stability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:27:34.862272+00:00
-- url     : https://prove2.me/submissions/3e88eec3-0a3b-4034-9b39-1b4dbd888347

import Mathlib
import Definitions.Def_PalmQueueing_Loynes_MultiserverQueue

open MeasureTheory Filter Topology PalmQueueing.Loynes

namespace LoynesMultiProof

private lemma monotone_order {s : ℕ} (v : Fin s → ℝ) : Monotone (order v) :=
  Tuple.monotone_sort v

private lemma sum_order {s : ℕ} (v : Fin s → ℝ) : ∑ j : Fin s, order v j = ∑ j : Fin s, v j :=
  Equiv.sum_comp (Tuple.sort v) v

private lemma order_mono {s : ℕ} {u v : Fin s → ℝ} (h : ∀ j, u j ≤ v j) :
    ∀ k, order u k ≤ order v k := by
  intro k
  by_contra hlt
  push Not at hlt
  let A : Finset (Fin s) := (Finset.Iic k).image (Tuple.sort v)
  let B : Finset (Fin s) := (Finset.Ici k).image (Tuple.sort u)
  have hA : A.card = (Finset.Iic k).card :=
    Finset.card_image_of_injective _ (Tuple.sort v).injective
  have hB : B.card = (Finset.Ici k).card :=
    Finset.card_image_of_injective _ (Tuple.sort u).injective
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    rcases Finset.mem_image.mp hiA with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hiB with ⟨b, hb, hab⟩
    have ha' : a ≤ k := Finset.mem_Iic.mp ha
    have hb' : k ≤ b := Finset.mem_Ici.mp hb
    have h1 : order u k ≤ order u b := monotone_order u hb'
    have h2 : order u b ≤ order v a := by
      change u (Tuple.sort u b) ≤ v (Tuple.sort v a)
      rw [hab]
      exact h _
    have h3 : order v a ≤ order v k := monotone_order v ha'
    linarith
  have hcard : (A ∪ B).card ≤ Fintype.card (Fin s) := Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint hdisj, hA, hB, Fin.card_Iic, Fin.card_Ici, Fintype.card_fin] at hcard
  omega

private lemma monotone_perm_eq {s : ℕ} {f g : Fin s → ℝ} (hf : Monotone f) (hg : Monotone g)
    (σ : Equiv.Perm (Fin s)) (hfg : f = g ∘ σ) : f = g := by
  funext k
  by_contra hne
  wlog hlt : f k < g k generalizing f g σ
  · have hgt : g k < f k := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
    exact this hg hf σ.symm (by ext x; simp [hfg]) (Ne.symm hne) hgt
  let A : Finset (Fin s) := (Finset.Iic k).image σ
  let B : Finset (Fin s) := Finset.Ici k
  have hA : A.card = (Finset.Iic k).card := Finset.card_image_of_injective _ σ.injective
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    rcases Finset.mem_image.mp hiA with ⟨a, ha, rfl⟩
    have ha' : a ≤ k := Finset.mem_Iic.mp ha
    have hb' : k ≤ σ a := Finset.mem_Ici.mp hiB
    have h1 : g k ≤ g (σ a) := hg hb'
    have h2 : g (σ a) = f a := by rw [hfg]; rfl
    have h3 : f a ≤ f k := hf ha'
    linarith
  have hcard : (A ∪ B).card ≤ Fintype.card (Fin s) := Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint hdisj, hA, Fin.card_Iic, Fin.card_Ici, Fintype.card_fin] at hcard
  omega

private lemma order_add_const {s : ℕ} (v : Fin s → ℝ) (c : ℝ) :
    order (fun j => v j + c) = fun k => order v k + c := by
  refine monotone_perm_eq (monotone_order _)
    (fun a b hab => add_le_add (monotone_order v hab) le_rfl)
    ((Tuple.sort (fun j => v j + c)).trans (Tuple.sort v).symm) ?_
  funext k
  simp [order]

private lemma continuous_order_coord {s : ℕ} (j : Fin s) :
    Continuous (fun v : Fin s → ℝ => order v j) := by
  rw [Metric.continuous_iff]
  intro v ε hε
  refine ⟨ε / 2, half_pos hε, fun w hw => ?_⟩
  rw [Real.dist_eq]
  have hdist : ∀ i, |w i - v i| < ε / 2 := fun i => by
    have hle : dist (w i) (v i) ≤ dist w v := dist_le_pi_dist w v i
    rw [← Real.dist_eq]
    exact lt_of_le_of_lt hle hw
  have h1 : ∀ i, v i + (-(ε / 2)) ≤ w i := fun i => by
    have := (abs_lt.mp (hdist i)).1; linarith
  have h2 : ∀ i, w i ≤ v i + ε / 2 := fun i => by
    have := (abs_lt.mp (hdist i)).2; linarith
  have hlow : order v j - ε / 2 ≤ order w j := by
    have := order_mono h1 j
    rw [order_add_const] at this
    linarith
  have hhigh : order w j ≤ order v j + ε / 2 := by
    have := order_mono h2 j
    rw [order_add_const] at this
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private lemma measurable_order_coord {s : ℕ} (j : Fin s) :
    Measurable (fun v : Fin s → ℝ => order v j) :=
  (continuous_order_coord j).measurable

private lemma fin_zero_le {s : ℕ} (hs : 0 < s) (j : Fin s) : (⟨0, hs⟩ : Fin s) ≤ j :=
  Nat.zero_le j.1

private lemma fin_le_last {s : ℕ} (hs : 0 < s) (j : Fin s) :
    j ≤ (⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ : Fin s) := by
  change j.1 ≤ s - 1
  have := j.isLt
  omega

private lemma order_zero_le {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) (j : Fin s) :
    order v ⟨0, hs⟩ ≤ v j := by
  have := monotone_order v (fin_zero_le hs ((Tuple.sort v).symm j))
  simpa [order] using this

private lemma exists_order_zero {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) :
    ∃ j : Fin s, order v ⟨0, hs⟩ = v j :=
  ⟨Tuple.sort v ⟨0, hs⟩, rfl⟩

private lemma le_order_last {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) (j : Fin s) :
    v j ≤ order v ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ := by
  have := monotone_order v (fin_le_last hs ((Tuple.sort v).symm j))
  simpa [order] using this

private lemma exists_order_last {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) :
    ∃ j : Fin s, order v ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = v j :=
  ⟨Tuple.sort v ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩, rfl⟩

private lemma kwStep_nonneg {s : ℕ} (sig tau : ℝ) (v : Fin s → ℝ) (j : Fin s) :
    0 ≤ kwStep sig tau v j := by
  unfold kwStep order
  exact le_max_right _ _

private lemma kwStep_mono {s : ℕ} (sig tau : ℝ) {u v : Fin s → ℝ} (h : ∀ j, u j ≤ v j) :
    ∀ j, kwStep sig tau u j ≤ kwStep sig tau v j := by
  intro j
  apply order_mono
  intro i
  exact max_le_max_right 0 (by linarith [h i])

private lemma kwM_succ_shift {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (n : ℕ) (ω : Ω) :
    kwM (s := s) shift sig tau (n + 1) (shift ω) =
      kwStep (sig ω) (tau ω) (kwM (s := s) shift sig tau n ω) := by
  simp [kwM]

private lemma kwM_nonneg {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (n : ℕ) (ω : Ω) (j : Fin s) :
    0 ≤ kwM shift sig tau n ω j := by
  cases n with
  | zero => simp [kwM]
  | succ n => exact kwStep_nonneg _ _ _ _

private lemma kwM_monotone_coord {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (kwM (s := s) shift sig tau n ω) := by
  cases n with
  | zero => intro a b _; simp [kwM]
  | succ n =>
    unfold kwM kwStep
    exact monotone_order _

private lemma kwM_mono_n {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) :
    ∀ (n : ℕ) (ω : Ω) (j : Fin s), kwM shift sig tau n ω j ≤ kwM shift sig tau (n + 1) ω j
  | 0, ω, j => by
    simpa [kwM] using kwM_nonneg shift sig tau 1 ω j
  | n + 1, ω, j => by
    exact kwStep_mono _ _ (fun i => kwM_mono_n shift sig tau n (shift.symm ω) i) j

private lemma kwM_monotone_n {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (ω : Ω) (j : Fin s) :
    Monotone (fun n => kwM shift sig tau n ω j) :=
  monotone_nat_of_le_succ (fun n => kwM_mono_n shift sig tau n ω j)

private lemma kwMinf_monotone_coord {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (ω : Ω) :
    Monotone (kwMinf (s := s) shift sig tau ω) := by
  intro a b hab
  exact iSup_mono fun n => EReal.coe_le_coe_iff.mpr (kwM_monotone_coord shift sig tau n ω hab)

private lemma kwM_measurable {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ)
    (hsigmeas : Measurable sig) (htaumeas : Measurable tau) :
    ∀ (n : ℕ) (j : Fin s), Measurable (fun ω => kwM shift sig tau n ω j)
  | 0, _ => measurable_const
  | n + 1, j => by
    have hinner : Measurable (fun ω => fun i : Fin s =>
        max (kwM shift sig tau n (shift.symm ω) i + sig (shift.symm ω) * kwUnit s i - tau (shift.symm ω)) 0) := by
      apply measurable_pi_lambda
      intro i
      have h1 : Measurable (fun ω => kwM shift sig tau n (shift.symm ω) i) :=
        (kwM_measurable shift sig tau hsigmeas htaumeas n i).comp shift.symm.measurable
      have h2 : Measurable (fun ω => sig (shift.symm ω) * kwUnit s i) :=
        (hsigmeas.comp shift.symm.measurable).mul measurable_const
      have h3 : Measurable (fun ω => tau (shift.symm ω)) :=
        htaumeas.comp shift.symm.measurable
      exact ((h1.add h2).sub h3).max measurable_const
    exact (measurable_order_coord j).comp hinner

private lemma kwMinf_measurable {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ)
    (hsigmeas : Measurable sig) (htaumeas : Measurable tau) (j : Fin s) :
    Measurable (fun ω => kwMinf shift sig tau ω j) := by
  unfold kwMinf
  exact Measurable.iSup fun n =>
    (measurable_coe_real_ereal).comp (kwM_measurable shift sig tau hsigmeas htaumeas n j)

private lemma kwUnit_nonneg {s : ℕ} (j : Fin s) : 0 ≤ kwUnit s j := by
  unfold kwUnit; split_ifs <;> norm_num

private lemma kwUnit_le_one {s : ℕ} (j : Fin s) : kwUnit s j ≤ 1 := by
  unfold kwUnit; split_ifs <;> norm_num

private lemma sum_kwUnit {s : ℕ} (hs : 0 < s) : ∑ j : Fin s, kwUnit s j = 1 := by
  have h0 : (⟨0, hs⟩ : Fin s) ∈ Finset.univ := Finset.mem_univ _
  rw [Finset.sum_eq_single ⟨0, hs⟩]
  · simp [kwUnit]
  · intro b _ hb
    unfold kwUnit
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    simp [this]
  · intro h; exact absurd h0 h

private lemma kwM_integrable {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (P0 : Measure Ω) (shift : Ω ≃ᵐ Ω) (hmp : MeasurePreserving shift P0 P0)
    (sig tau : Ω → ℝ) (hsigmeas : Measurable sig) (htaumeas : Measurable tau)
    (hsig0 : ∀ ω, 0 ≤ sig ω) (htau0 : ∀ ω, 0 ≤ tau ω)
    (hsigInt : Integrable sig P0) :
    ∀ (n : ℕ) (j : Fin s), Integrable (fun ω => kwM shift sig tau n ω j) P0
  | 0, _ => by
    simp [kwM]
  | n + 1, j => by
    have hmp_symm : MeasurePreserving shift.symm P0 P0 := hmp.symm shift
    have hsum_int : Integrable (fun ω => ∑ i : Fin s, (kwM shift sig tau n (shift.symm ω) i + sig (shift.symm ω))) P0 := by
      apply integrable_finsetSum
      intro i _
      have hi0 : Integrable (fun ω => kwM shift sig tau n ω i) P0 :=
        kwM_integrable P0 shift hmp sig tau hsigmeas htaumeas hsig0 htau0 hsigInt n i
      have hi : Integrable (fun ω => kwM shift sig tau n (shift.symm ω) i) P0 :=
        (hmp_symm.integrable_comp_emb shift.symm.measurableEmbedding).mpr hi0
      have hs' : Integrable (fun ω => sig (shift.symm ω)) P0 :=
        (hmp_symm.integrable_comp_emb shift.symm.measurableEmbedding).mpr hsigInt
      exact hi.add hs'
    refine Integrable.mono' hsum_int
      (kwM_measurable shift sig tau hsigmeas htaumeas (n + 1) j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (kwM_nonneg shift sig tau (n + 1) ω j)]
    have hle_sum : kwM shift sig tau (n + 1) ω j ≤ ∑ i : Fin s, kwM shift sig tau (n + 1) ω i :=
      Finset.single_le_sum (fun i _ => kwM_nonneg shift sig tau (n + 1) ω i) (Finset.mem_univ j)
    refine le_trans hle_sum ?_
    change ∑ i : Fin s, order (fun k => max (kwM shift sig tau n (shift.symm ω) k +
        sig (shift.symm ω) * kwUnit s k - tau (shift.symm ω)) 0) i ≤ _
    rw [sum_order]
    apply Finset.sum_le_sum
    intro i _
    apply max_le
    · have h1 : sig (shift.symm ω) * kwUnit s i ≤ sig (shift.symm ω) :=
        mul_le_of_le_one_right (hsig0 _) (kwUnit_le_one i)
      linarith [htau0 (shift.symm ω)]
    · linarith [kwM_nonneg shift sig tau n (shift.symm ω) i, hsig0 (shift.symm ω)]

private lemma kwMinf_eq_top_iff {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (ω : Ω) (j : Fin s) :
    kwMinf shift sig tau ω j = (⊤ : EReal) ↔ ∀ M : ℝ, ∃ n : ℕ, M ≤ kwM shift sig tau n ω j := by
  constructor
  · intro h M
    by_contra hnot
    push Not at hnot
    have hle : kwMinf shift sig tau ω j ≤ (M : EReal) :=
      iSup_le fun n => EReal.coe_le_coe_iff.mpr (le_of_lt (hnot n))
    rw [h] at hle
    exact EReal.coe_ne_top M (top_le_iff.mp hle)
  · intro h
    unfold kwMinf
    rw [iSup_eq_top]
    intro b hb
    rcases EReal.exists_between_coe_real hb with ⟨r, hbr, _⟩
    rcases h r with ⟨n, hn⟩
    exact ⟨n, lt_of_lt_of_le hbr (EReal.coe_le_coe_iff.mpr hn)⟩

private lemma kwMinf_ne_top_iff {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (ω : Ω) (j : Fin s) :
    kwMinf shift sig tau ω j ≠ (⊤ : EReal) ↔ ∃ C : ℝ, ∀ n : ℕ, kwM shift sig tau n ω j ≤ C := by
  rw [ne_eq, kwMinf_eq_top_iff]
  push Not
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun n => le_of_lt (hM n)⟩
  · rintro ⟨C, hC⟩
    exact ⟨C + 1, fun n => by linarith [hC n]⟩

private lemma preimage_A0 {Ω : Type*} [MeasurableSpace Ω] {s : ℕ} (hs : 0 < s)
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) :
    shift ⁻¹' {ω | kwMinf shift sig tau ω ⟨0, hs⟩ = (⊤ : EReal)} =
      {ω | kwMinf shift sig tau ω ⟨0, hs⟩ = (⊤ : EReal)} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, kwMinf_eq_top_iff]
  constructor
  · intro h M
    rcases h (max (M + sig ω - tau ω) 0 + 1) with ⟨n, hn⟩
    cases n with
    | zero =>
      simp only [kwM] at hn
      have : (0 : ℝ) < max (M + sig ω - tau ω) 0 + 1 := by
        linarith [le_max_right (M + sig ω - tau ω) 0]
      linarith
    | succ n =>
      rw [kwM_succ_shift] at hn
      have hle : kwStep (sig ω) (tau ω) (kwM shift sig tau n ω) ⟨0, hs⟩ ≤
          max (kwM shift sig tau n ω ⟨0, hs⟩ + sig ω * kwUnit s ⟨0, hs⟩ - tau ω) 0 :=
        order_zero_le hs _ ⟨0, hs⟩
      have h1 : max (M + sig ω - tau ω) 0 + 1 ≤
          max (kwM shift sig tau n ω ⟨0, hs⟩ + sig ω - tau ω) 0 := by
        have hu : kwUnit s ⟨0, hs⟩ = 1 := by simp [kwUnit]
        rw [hu, mul_one] at hle
        exact le_trans hn hle
      have h2 : M + sig ω - tau ω < kwM shift sig tau n ω ⟨0, hs⟩ + sig ω - tau ω := by
        by_contra hle'
        push Not at hle'
        have : max (kwM shift sig tau n ω ⟨0, hs⟩ + sig ω - tau ω) 0 ≤ max (M + sig ω - tau ω) 0 :=
          max_le_max_right 0 hle'
        linarith
      exact ⟨n, by linarith⟩
  · intro h M
    rcases h (M + tau ω + |sig ω|) with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [kwM_succ_shift]
    rcases exists_order_zero hs (fun j => max (kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω) 0) with ⟨j, hj⟩
    rw [kwStep, hj]
    have hmj : kwM shift sig tau n ω ⟨0, hs⟩ ≤ kwM shift sig tau n ω j :=
      kwM_monotone_coord shift sig tau n ω (fin_zero_le hs j)
    have hsig_bound : -|sig ω| ≤ sig ω * kwUnit s j := by
      unfold kwUnit
      split_ifs
      · linarith [neg_abs_le (sig ω)]
      · simp [abs_nonneg]
    exact le_trans (by linarith) (le_max_left _ 0)

private lemma preimage_As {Ω : Type*} [MeasurableSpace Ω] {s : ℕ} (hs : 0 < s)
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (hsig0 : ∀ ω, 0 ≤ sig ω) :
    shift ⁻¹' {ω | kwMinf shift sig tau ω ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = (⊤ : EReal)} =
      {ω | kwMinf shift sig tau ω ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = (⊤ : EReal)} := by
  let js : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, kwMinf_eq_top_iff]
  constructor
  · intro h M
    rcases h (max (M + sig ω - tau ω) 0 + 1) with ⟨n, hn⟩
    cases n with
    | zero =>
      simp only [kwM] at hn
      have : (0 : ℝ) < max (M + sig ω - tau ω) 0 + 1 := by
        linarith [le_max_right (M + sig ω - tau ω) 0]
      linarith
    | succ n =>
      rw [kwM_succ_shift] at hn
      rcases exists_order_last hs (fun j => max (kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω) 0) with ⟨j, hj⟩
      rw [kwStep, hj] at hn
      have hmj : kwM shift sig tau n ω j ≤ kwM shift sig tau n ω js :=
        kwM_monotone_coord shift sig tau n ω (fin_le_last hs j)
      have hsu : sig ω * kwUnit s j ≤ sig ω := mul_le_of_le_one_right (hsig0 ω) (kwUnit_le_one j)
      have h1 : max (M + sig ω - tau ω) 0 + 1 ≤ max (kwM shift sig tau n ω js + sig ω - tau ω) 0 :=
        le_trans hn (max_le_max_right 0 (by linarith))
      have h2 : M + sig ω - tau ω < kwM shift sig tau n ω js + sig ω - tau ω := by
        by_contra hle'
        push Not at hle'
        have : max (kwM shift sig tau n ω js + sig ω - tau ω) 0 ≤ max (M + sig ω - tau ω) 0 :=
          max_le_max_right 0 hle'
        linarith
      exact ⟨n, by linarith⟩
  · intro h M
    rcases h (M + tau ω) with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [kwM_succ_shift]
    have hle : max (kwM shift sig tau n ω js + sig ω * kwUnit s js - tau ω) 0 ≤
        kwStep (sig ω) (tau ω) (kwM shift sig tau n ω) js :=
      le_order_last hs (fun j => max (kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω) 0) js
    have hsu : 0 ≤ sig ω * kwUnit s js := mul_nonneg (hsig0 ω) (kwUnit_nonneg js)
    exact le_trans (by linarith) (le_trans (le_max_left _ 0) hle)

private lemma kwM_last_succ_shift {Ω : Type*} [MeasurableSpace Ω] {s : ℕ} (hs : 0 < s)
    (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (hsig0 : ∀ ω, 0 ≤ sig ω) (n : ℕ) (ω : Ω) :
    kwM shift sig tau (n + 1) (shift ω) ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ =
      max (kwM shift sig tau n ω ⟨0, hs⟩ + sig ω - tau ω)
          (max (kwM shift sig tau n ω ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ - tau ω) 0) := by
  let j0 : Fin s := ⟨0, hs⟩
  let js : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  rw [kwM_succ_shift]
  apply le_antisymm
  · rcases exists_order_last hs (fun j => max (kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω) 0) with ⟨j, hj⟩
    rw [kwStep, hj]
    by_cases hj0 : (j : ℕ) = 0
    · have hj_eq : j = j0 := Fin.ext hj0
      rw [hj_eq]
      have hu : kwUnit s j0 = 1 := by simp [kwUnit, j0]
      rw [hu, mul_one]
      exact max_le (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    · have hu : kwUnit s j = 0 := by simp [kwUnit, hj0]
      rw [hu, mul_zero, add_zero]
      have hmj : kwM shift sig tau n ω j ≤ kwM shift sig tau n ω js :=
        kwM_monotone_coord shift sig tau n ω (fin_le_last hs j)
      exact le_trans (max_le_max_right 0 (by linarith)) (le_max_right _ _)
  · apply max_le
    · have h1 := le_order_last hs (fun j => max (kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω) 0) j0
      have hu : kwUnit s j0 = 1 := by simp [kwUnit, j0]
      rw [hu, mul_one] at h1
      exact le_trans (le_max_left _ 0) h1
    · apply max_le
      · have h2 := le_order_last hs (fun j => max (kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω) 0) js
        have hsu : 0 ≤ sig ω * kwUnit s js := mul_nonneg (hsig0 ω) (kwUnit_nonneg js)
        exact le_trans (by change kwM shift sig tau n ω js - tau ω ≤ _; linarith)
          (le_trans (le_max_left _ 0) h2)
      · exact kwStep_nonneg _ _ _ _

end LoynesMultiProof

open LoynesMultiProof in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {s : ℕ} (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω ≃ᵐ Ω) (herg : Ergodic shift P0)
    (sig tau : Ω → ℝ) (hsigmeas : Measurable sig) (htaumeas : Measurable tau)
    (hsig0 : ∀ ω, 0 ≤ sig ω) (htau0 : ∀ ω, 0 ≤ tau ω)
    (hsigInt : Integrable sig P0) (htauInt : Integrable tau P0)
    (hstab : (∫ ω, sig ω ∂P0) < (s : ℝ) * ∫ ω, tau ω ∂P0) :
    ∀ᵐ ω ∂P0, ∀ j : Fin s, kwMinf shift sig tau ω j ≠ (⊤ : EReal) := by
  by_cases hs : s = 0
  · subst hs
    exact Eventually.of_forall fun _ j => Fin.elim0 j
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  let j0 : Fin s := ⟨0, hspos⟩
  let js : Fin s := ⟨s - 1, Nat.sub_lt hspos zero_lt_one⟩
  have hmp : MeasurePreserving shift P0 P0 := herg.toMeasurePreserving
  have hsig_int_nonneg : 0 ≤ ∫ ω, sig ω ∂P0 := integral_nonneg hsig0
  have htau_int_pos : 0 < ∫ ω, tau ω ∂P0 := by
    have hs_pos_real : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hspos
    nlinarith
  -- Step 1: Show ∀ᵐ ω ∂P0, kwMinf ω j0 ≠ ⊤
  have hA0_meas : MeasurableSet {ω | kwMinf shift sig tau ω j0 = (⊤ : EReal)} :=
    (kwMinf_measurable shift sig tau hsigmeas htaumeas j0) (measurableSet_singleton (⊤ : EReal))
  have hA0_inv : shift ⁻¹' {ω | kwMinf shift sig tau ω j0 = (⊤ : EReal)} =
      {ω | kwMinf shift sig tau ω j0 = (⊤ : EReal)} :=
    preimage_A0 hspos shift sig tau
  have hA0_ae : ∀ᵐ ω ∂P0, kwMinf shift sig tau ω j0 ≠ (⊤ : EReal) := by
    rcases herg.ae_empty_or_univ hA0_meas hA0_inv with hempty | huniv
    · filter_upwards [hempty] with ω hω
      intro h; exact (eq_iff_iff.mp hω).mp h
    · exfalso
      have hall_top : ∀ᵐ ω ∂P0, kwMinf shift sig tau ω j0 = (⊤ : EReal) := by
        filter_upwards [huniv] with ω hω
        exact (eq_iff_iff.mp hω).mpr trivial
      let f : ℕ → Ω → ℝ := fun n ω =>
        ∑ j : Fin s, min (kwM shift sig tau n ω j) (tau ω - sig ω * kwUnit s j)
      let bound : Ω → ℝ := fun ω => (s : ℝ) * (tau ω + sig ω)
      have hbound_int : Integrable bound P0 := (htauInt.add hsigInt).const_mul (s : ℝ)
      have hf_meas : ∀ n, AEStronglyMeasurable (f n) P0 := fun n => by
        refine (Finset.measurable_sum Finset.univ fun j _ => ?_).aestronglyMeasurable
        exact (kwM_measurable shift sig tau hsigmeas htaumeas n j).min
          (htaumeas.sub (hsigmeas.mul measurable_const))
      have hf_bound : ∀ n, ∀ᵐ ω ∂P0, ‖f n ω‖ ≤ bound ω := fun n => by
        filter_upwards with ω
        calc ‖f n ω‖
            ≤ ∑ j : Fin s, ‖min (kwM shift sig tau n ω j) (tau ω - sig ω * kwUnit s j)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _j : Fin s, (tau ω + sig ω) := by
              apply Finset.sum_le_sum
              intro j _
              rw [Real.norm_eq_abs, abs_le]
              have hsu_nonneg : 0 ≤ sig ω * kwUnit s j := mul_nonneg (hsig0 ω) (kwUnit_nonneg j)
              have hsu_le : sig ω * kwUnit s j ≤ sig ω :=
                mul_le_of_le_one_right (hsig0 ω) (kwUnit_le_one j)
              constructor
              · exact le_min (by linarith [kwM_nonneg shift sig tau n ω j, htau0 ω, hsig0 ω])
                  (by linarith [htau0 ω])
              · exact le_trans (min_le_right _ _) (by linarith)
          _ = bound ω := by simp [bound]; ring
      have hf_lim : ∀ᵐ ω ∂P0, Tendsto (fun n => f n ω) atTop
          (𝓝 ((s : ℝ) * tau ω - sig ω)) := by
        filter_upwards [hall_top] with ω hω
        have hsum_eq : (s : ℝ) * tau ω - sig ω =
            ∑ j : Fin s, (tau ω - sig ω * kwUnit s j) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum, sum_kwUnit hspos, mul_one]
        rw [hsum_eq]
        apply tendsto_finsetSum
        intro j _
        have htop_j : kwMinf shift sig tau ω j = (⊤ : EReal) :=
          top_le_iff.mp (hω ▸ kwMinf_monotone_coord shift sig tau ω (fin_zero_le hspos j))
        rcases (kwMinf_eq_top_iff shift sig tau ω j).mp htop_j (tau ω - sig ω * kwUnit s j) with ⟨N, hN⟩
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hge : tau ω - sig ω * kwUnit s j ≤ kwM shift sig tau n ω j :=
          le_trans hN (kwM_monotone_n shift sig tau ω j hn)
        exact (min_eq_right hge).symm
      have htend : Tendsto (fun n => ∫ ω, f n ω ∂P0) atTop
          (𝓝 (∫ ω, ((s : ℝ) * tau ω - sig ω) ∂P0)) :=
        tendsto_integral_of_dominated_convergence bound hf_meas hbound_int hf_bound hf_lim
      have hf_int_le_zero : ∀ n, ∫ ω, f n ω ∂P0 ≤ 0 := fun n => by
        have hident : ∀ ω, f n ω =
            (∑ j : Fin s, kwM shift sig tau n ω j) -
            (∑ j : Fin s, kwM shift sig tau (n + 1) (shift ω) j) := fun ω => by
          have hstep : ∑ j : Fin s, kwM shift sig tau (n + 1) (shift ω) j =
              ∑ j : Fin s, max (kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω) 0 := by
            rw [kwM_succ_shift]; exact sum_order _
          rw [hstep, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          have hmin : ∀ x b : ℝ, min x b = x - max (x - b) 0 := fun x b => by
            rcases le_total x b with hxb | hbx
            · rw [min_eq_left hxb, max_eq_right (by linarith)]; ring
            · rw [min_eq_right hbx, max_eq_left (by linarith)]; ring
          have harg : kwM shift sig tau n ω j + sig ω * kwUnit s j - tau ω =
              kwM shift sig tau n ω j - (tau ω - sig ω * kwUnit s j) := by ring
          rw [harg]
          exact hmin (kwM shift sig tau n ω j) (tau ω - sig ω * kwUnit s j)
        have hint_n : Integrable (fun ω => ∑ j : Fin s, kwM shift sig tau n ω j) P0 :=
          integrable_finsetSum _ fun j _ =>
            kwM_integrable P0 shift hmp sig tau hsigmeas htaumeas hsig0 htau0 hsigInt n j
        have hint_n1 : Integrable (fun ω => ∑ j : Fin s, kwM shift sig tau (n + 1) ω j) P0 :=
          integrable_finsetSum _ fun j _ =>
            kwM_integrable P0 shift hmp sig tau hsigmeas htaumeas hsig0 htau0 hsigInt (n + 1) j
        have hint_n1_shift : Integrable (fun ω => ∑ j : Fin s, kwM shift sig tau (n + 1) (shift ω) j) P0 :=
          (hmp.integrable_comp_emb shift.measurableEmbedding).mpr hint_n1
        have heq : ∫ ω, f n ω ∂P0 =
            (∫ ω, (∑ j : Fin s, kwM shift sig tau n ω j) ∂P0) -
            (∫ ω, (∑ j : Fin s, kwM shift sig tau (n + 1) (shift ω) j) ∂P0) := by
          simp_rw [hident]
          exact integral_sub hint_n hint_n1_shift
        rw [heq, hmp.integral_comp' (g := fun ω => ∑ j : Fin s, kwM shift sig tau (n + 1) ω j)]
        have hle : ∫ ω, (∑ j : Fin s, kwM shift sig tau n ω j) ∂P0 ≤
            ∫ ω, (∑ j : Fin s, kwM shift sig tau (n + 1) ω j) ∂P0 :=
          integral_mono hint_n hint_n1 fun ω =>
            Finset.sum_le_sum fun j _ => kwM_mono_n shift sig tau n ω j
        linarith
      have hlim_le : ∫ ω, ((s : ℝ) * tau ω - sig ω) ∂P0 ≤ 0 :=
        le_of_tendsto htend (Eventually.of_forall hf_int_le_zero)
      have hsplit : ∫ ω, ((s : ℝ) * tau ω - sig ω) ∂P0 =
          (s : ℝ) * (∫ ω, tau ω ∂P0) - ∫ ω, sig ω ∂P0 := by
        rw [integral_sub (htauInt.const_mul (s : ℝ)) hsigInt, integral_const_mul]
      linarith
  -- Step 2: Show ∀ᵐ ω ∂P0, kwMinf ω js ≠ ⊤
  have hAs_meas : MeasurableSet {ω | kwMinf shift sig tau ω js = (⊤ : EReal)} :=
    (kwMinf_measurable shift sig tau hsigmeas htaumeas js) (measurableSet_singleton (⊤ : EReal))
  have hAs_inv : shift ⁻¹' {ω | kwMinf shift sig tau ω js = (⊤ : EReal)} =
      {ω | kwMinf shift sig tau ω js = (⊤ : EReal)} :=
    preimage_As hspos shift sig tau hsig0
  have hAs_ae : ∀ᵐ ω ∂P0, kwMinf shift sig tau ω js ≠ (⊤ : EReal) := by
    rcases herg.ae_empty_or_univ hAs_meas hAs_inv with hempty | huniv
    · filter_upwards [hempty] with ω hω
      intro h; exact (eq_iff_iff.mp hω).mp h
    · exfalso
      have hs_top : ∀ᵐ ω ∂P0, kwMinf shift sig tau ω js = (⊤ : EReal) := by
        filter_upwards [huniv] with ω hω
        exact (eq_iff_iff.mp hω).mpr trivial
      let g : ℕ → Ω → ℝ := fun n ω =>
        kwM shift sig tau (n + 1) (shift ω) js - kwM shift sig tau n ω js
      let bound : Ω → ℝ := fun ω => tau ω + sig ω
      have hbound_int : Integrable bound P0 := htauInt.add hsigInt
      have hg_meas : ∀ n, AEStronglyMeasurable (g n) P0 := fun n =>
        (((kwM_measurable shift sig tau hsigmeas htaumeas (n + 1) js).comp shift.measurable).sub
          (kwM_measurable shift sig tau hsigmeas htaumeas n js)).aestronglyMeasurable
      have hg_eq : ∀ n ω, g n ω =
          max (kwM shift sig tau n ω j0 + sig ω - kwM shift sig tau n ω js - tau ω)
              (max (- tau ω) (- kwM shift sig tau n ω js)) := fun n ω => by
        dsimp only [g]
        rw [kwM_last_succ_shift hspos shift sig tau hsig0 n ω]
        have hsub : ∀ a b c d : ℝ, max a (max b c) - d = max (a - d) (max (b - d) (c - d)) :=
          fun a b c d => by rw [max_sub_sub_right, max_sub_sub_right]
        rw [hsub]
        congr 1
        · ring
        · congr 1 <;> ring
      have hg_bound : ∀ n, ∀ᵐ ω ∂P0, ‖g n ω‖ ≤ bound ω := fun n => by
        filter_upwards with ω
        rw [hg_eq n ω, Real.norm_eq_abs, abs_le]
        have hmle : kwM shift sig tau n ω j0 ≤ kwM shift sig tau n ω js :=
          kwM_monotone_coord shift sig tau n ω (fin_zero_le hspos js)
        constructor
        · exact le_trans (by linarith [hsig0 ω]) (le_trans (le_max_left _ _) (le_max_right _ _))
        · apply max_le
          · linarith [htau0 ω]
          · exact max_le (by linarith [htau0 ω, hsig0 ω])
              (by linarith [kwM_nonneg shift sig tau n ω js, htau0 ω, hsig0 ω])
      have hg_lim : ∀ᵐ ω ∂P0, Tendsto (fun n => g n ω) atTop (𝓝 (- tau ω)) := by
        filter_upwards [hA0_ae, hs_top] with ω hω0 hωs
        rcases (kwMinf_ne_top_iff shift sig tau ω j0).mp hω0 with ⟨C, hC⟩
        rcases (kwMinf_eq_top_iff shift sig tau ω js).mp hωs (max (C + sig ω) (tau ω)) with ⟨N, hN⟩
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [hg_eq n ω]
        have hge : max (C + sig ω) (tau ω) ≤ kwM shift sig tau n ω js :=
          le_trans hN (kwM_monotone_n shift sig tau ω js hn)
        have h1 : kwM shift sig tau n ω j0 + sig ω - kwM shift sig tau n ω js - tau ω ≤ - tau ω := by
          linarith [hC n, le_max_left (C + sig ω) (tau ω)]
        have h2 : - kwM shift sig tau n ω js ≤ - tau ω := by
          linarith [le_max_right (C + sig ω) (tau ω)]
        rw [max_eq_left h2, max_eq_right h1]
      have htend : Tendsto (fun n => ∫ ω, g n ω ∂P0) atTop (𝓝 (∫ ω, (- tau ω) ∂P0)) :=
        tendsto_integral_of_dominated_convergence bound hg_meas hbound_int hg_bound hg_lim
      have hg_int_nonneg : ∀ n, 0 ≤ ∫ ω, g n ω ∂P0 := fun n => by
        have hint_n := kwM_integrable P0 shift hmp sig tau hsigmeas htaumeas hsig0 htau0 hsigInt n js
        have hint_n1 := kwM_integrable P0 shift hmp sig tau hsigmeas htaumeas hsig0 htau0 hsigInt (n + 1) js
        have hint_n1_shift : Integrable (fun ω => kwM shift sig tau (n + 1) (shift ω) js) P0 :=
          (hmp.integrable_comp_emb shift.measurableEmbedding).mpr hint_n1
        have heq : ∫ ω, g n ω ∂P0 =
            (∫ ω, kwM shift sig tau (n + 1) (shift ω) js ∂P0) -
            (∫ ω, kwM shift sig tau n ω js ∂P0) :=
          integral_sub hint_n1_shift hint_n
        rw [heq, hmp.integral_comp' (g := fun ω => kwM shift sig tau (n + 1) ω js)]
        have hle := integral_mono hint_n hint_n1 fun ω => kwM_mono_n shift sig tau n ω js
        linarith
      have hlim_nonneg : 0 ≤ ∫ ω, (- tau ω) ∂P0 :=
        ge_of_tendsto htend (Eventually.of_forall hg_int_nonneg)
      rw [integral_neg] at hlim_nonneg
      linarith
  -- Step 3: Conclude for all j : Fin s by monotonicity of kwMinf in j
  filter_upwards [hAs_ae] with ω hω j htop
  have hle : kwMinf shift sig tau ω j ≤ kwMinf shift sig tau ω js :=
    kwMinf_monotone_coord shift sig tau ω (fin_le_last hspos j)
  rw [htop] at hle
  exact hω (top_le_iff.mp hle)

#print axioms solution
