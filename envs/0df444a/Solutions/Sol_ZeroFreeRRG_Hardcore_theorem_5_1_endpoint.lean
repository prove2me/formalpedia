-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.theorem_5_1_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:27:16.476881+00:00
-- url     : https://prove2.me/submissions/837c92da-6ef8-421a-a69d-92f444200828

import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_7
import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
set_option autoImplicit false
open Finset
open scoped Classical

private noncomputable def posJumps (n k : ℕ) [NeZero n] : Finset (Fin n) :=
  (Finset.Icc 1 k).image (fun j : ℕ => Fin.ofNat n j)

private noncomputable def negJumps (n k : ℕ) [NeZero n] : Finset (Fin n) :=
  (posJumps n k).image Neg.neg

private theorem posJumps_mem_val (n k : ℕ) [NeZero n] (hk : k < n) (v : Fin n) :
    v ∈ posJumps n k ↔ 1 ≤ v.val ∧ v.val ≤ k := by
  classical
  unfold posJumps
  constructor
  · intro hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    have hj' := Finset.mem_Icc.mp hj
    have hjn : j < n := lt_of_le_of_lt hj'.2 hk
    simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hjn] using hj'
  · intro hv
    refine Finset.mem_image.mpr ⟨v.val, Finset.mem_Icc.mpr hv, ?_⟩
    apply Fin.ext
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt v.isLt]

private theorem posJumps_card (n k : ℕ) [NeZero n] (hk : k < n) : (posJumps n k).card = k := by
  classical
  unfold posJumps
  rw [Finset.card_image_iff.mpr ?_, Nat.card_Icc]
  · omega
  · intro i hi j hj heq
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    have hv := congrArg Fin.val heq
    simpa [Fin.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt hi'.2 hk),
      Nat.mod_eq_of_lt (lt_of_le_of_lt hj'.2 hk)] using hv

private theorem pos_nonzero (n k : ℕ) [NeZero n] (hk : k < n) {v : Fin n}
    (hv : v ∈ posJumps n k) : v ≠ 0 := by
  have h := (posJumps_mem_val n k hk v).mp hv
  intro he
  subst v
  simpa using h.1

private theorem pos_neg_disjoint (n k : ℕ) [NeZero n] (h2 : 2*k < n) :
    Disjoint (posJumps n k) (negJumps n k) := by
  classical
  have hk : k < n := by omega
  apply Finset.disjoint_left.mpr
  intro v hv hvneg
  obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hvneg
  have hv' := (posJumps_mem_val n k hk v).mp hv
  have hw' := (posJumps_mem_val n k hk w).mp hw
  have hw0 := pos_nonzero n k hk hw
  have hvv : v.val = n - w.val := by
    rw [← heq, Fin.val_neg, if_neg hw0]
  omega

private theorem negJumps_card (n k : ℕ) [NeZero n] (hk : k < n) : (negJumps n k).card = k := by
  classical
  unfold negJumps
  rw [Finset.card_image_of_injective _ (neg_injective : Function.Injective (Neg.neg : Fin n → Fin n)), posJumps_card n k hk]

private noncomputable def jumps (n k : ℕ) [NeZero n] : Finset (Fin n) :=
  posJumps n k ∪ negJumps n k

private theorem jumps_neg (n k : ℕ) [NeZero n] (v : Fin n) :
    -v ∈ jumps n k ↔ v ∈ jumps n k := by
  classical
  simp only [jumps, Finset.mem_union, negJumps, Finset.mem_image]
  constructor
  · rintro (h | ⟨w, hw, heq⟩)
    · exact Or.inr ⟨-v, h, by simp⟩
    · have : w = v := by simpa using congrArg Neg.neg heq
      exact Or.inl (this ▸ hw)
  · rintro (h | ⟨w, hw, heq⟩)
    · exact Or.inr ⟨v, h, rfl⟩
    · have : w = -v := by simpa using congrArg Neg.neg heq
      exact Or.inl (this ▸ hw)

private theorem jumps_card (n k : ℕ) [NeZero n] (h2 : 2*k < n) :
    (jumps n k).card = 2*k := by
  have hk : k < n := by omega
  simp [jumps, Finset.card_union_of_disjoint (pos_neg_disjoint n k h2),
    posJumps_card n k hk, negJumps_card n k hk, two_mul]

private theorem jumps_zero (n k : ℕ) [NeZero n] (h2 : 2*k < n) :
    0 ∉ jumps n k := by
  have hk : k < n := by omega
  simp only [jumps, Finset.mem_union, not_or, negJumps, Finset.mem_image]
  constructor
  · exact fun h => pos_nonzero n k hk h rfl
  · rintro ⟨w, hw, heq⟩
    have hw0 : w = 0 := neg_eq_zero.mp heq
    exact pos_nonzero n k hk hw hw0

private theorem degree_of_jumps (n : ℕ) [NeZero n] (J : Finset (Fin n))
    (hzero : 0 ∉ J) (hsym : ∀ v, -v ∈ J ↔ v ∈ J) :
    ∃ G : SimpleGraph (Fin n), G.IsRegularOfDegree J.card := by
  classical
  let G := SimpleGraph.circulantGraph (J : Set (Fin n))
  have hneighbor (v : Fin n) : G.neighborFinset v = J.image (fun j => v + j) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, G, SimpleGraph.circulantGraph_adj,
      Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨hne, h | h⟩
      · refine ⟨w-v, ?_, by simp⟩
        apply (hsym (w-v)).mp
        simpa [neg_sub] using h
      · refine ⟨w-v, ?_, by simp⟩
        simpa using h
    · rintro ⟨j,hj,rfl⟩
      constructor
      · intro he
        have : j = 0 := by simpa using (congrArg (fun z => z-v) he).symm
        exact hzero (this ▸ hj)
      · right
        simpa using hj
  refine ⟨G, ?_⟩
  intro v
  have hcard := congrArg Finset.card (hneighbor v)
  rw [Finset.card_image_of_injective _ (add_right_injective v)] at hcard
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  convert hcard using 1
  congr 1
  ext u
  simp only [SimpleGraph.mem_neighborFinset]

private theorem antipode_val (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (Fin.ofNat n (n / 2)).val = n / 2 := by
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt]
  omega

private theorem antipode_neg (n : ℕ) [NeZero n] (hn : 2 ≤ n) (he : Even n) :
    -(Fin.ofNat n (n / 2)) = Fin.ofNat n (n / 2) := by
  have hv := antipode_val n hn
  have hne : Fin.ofNat n (n / 2) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    omega
  apply Fin.ext
  rw [Fin.val_neg, if_neg hne, hv]
  obtain ⟨m,hm⟩ := he
  omega

private theorem antipode_not_jumps (n k : ℕ) [NeZero n] (h : 2*k+1 < n)
    (he : Even n) : Fin.ofNat n (n/2) ∉ jumps n k := by
  have hn : 2 ≤ n := by
    obtain ⟨m,hm⟩ := he
    have : 0 < n := NeZero.pos n
    omega
  have hk : k < n := by omega
  have hv := antipode_val n hn
  have hnotpos : Fin.ofNat n (n/2) ∉ posJumps n k := by
    intro hm
    have h' := (posJumps_mem_val n k hk _).mp hm
    rw [hv] at h'
    omega
  intro hm
  rcases Finset.mem_union.mp hm with hp | hm
  · exact hnotpos hp
  · obtain ⟨w,hw,hw'⟩ := Finset.mem_image.mp hm
    have : w = Fin.ofNat n (n/2) := by
      have hh := congrArg Neg.neg hw'
      calc
        w = -(Fin.ofNat n (n/2)) := by simpa using hh
        _ = Fin.ofNat n (n/2) := antipode_neg n hn he
    exact hnotpos (this ▸ hw)

private theorem regular_of_even_degree (n k : ℕ) [NeZero n] (h : 2*k < n) :
    ∃ G : SimpleGraph (Fin n), G.IsRegularOfDegree (2*k) := by
  simpa [jumps_card n k h] using degree_of_jumps n (jumps n k) (jumps_zero n k h) (jumps_neg n k)

private theorem regular_of_odd_degree (n k : ℕ) [NeZero n] (h : 2*k+1 < n)
    (he : Even n) : ∃ G : SimpleGraph (Fin n), G.IsRegularOfDegree (2*k+1) := by
  classical
  have hn : 2 ≤ n := by
    obtain ⟨m,hm⟩ := he
    have : 0 < n := NeZero.pos n
    omega
  let a := Fin.ofNat n (n/2)
  let J := insert a (jumps n k)
  have hz : 0 ∉ J := by
    simp only [J, Finset.mem_insert, not_or]
    constructor
    · intro heq
      have hh := congrArg Fin.val heq
      simp only [Fin.val_zero, a, antipode_val n hn] at hh
      omega
    · exact jumps_zero n k (by omega)
  have hs : ∀ v, -v ∈ J ↔ v ∈ J := by
    intro v
    simp only [J, Finset.mem_insert, jumps_neg]
    have ha : -a = a := antipode_neg n hn he
    constructor
    · rintro (hva | hv)
      · left
        have := congrArg Neg.neg hva
        simpa [ha] using this
      · exact Or.inr hv
    · rintro (hva | hv)
      · left
        simpa [hva] using ha
      · exact Or.inr hv
  have hc : J.card = 2*k+1 := by
    have ha : a ∉ jumps n k := antipode_not_jumps n k h he
    change (insert a (jumps n k)).card = _
    rw [Finset.card_insert_of_notMem ha, jumps_card n k (by omega)]
  simpa [hc] using degree_of_jumps n J hz hs

theorem exists_regular_graph_of_even_mul (n d : ℕ) (h : d < n) (he : Even (n*d)) :
    ∃ G : SimpleGraph (Fin n), G.IsRegularOfDegree d := by
  classical
  have hn : 0 < n := by omega
  letI : NeZero n := ⟨by omega⟩
  by_cases hd : Even d
  · obtain ⟨k,hk⟩ := hd
    have h' : 2*k < n := by omega
    have heq : d = 2*k := by omega
    rw [heq]
    exact regular_of_even_degree n k h'
  · have hne : Even n := by
      rcases (Nat.even_mul.mp he) with hn | hd'
      · exact hn
      · exact (hd hd').elim
    obtain ⟨k,hk⟩ : ∃ k, d = 2*k+1 := by
      have hmod : d % 2 = 1 := by
        have : ¬ d % 2 = 0 := by simpa [Nat.even_iff] using hd
        omega
      exact ⟨d/2, by omega⟩
    have h' : 2*k+1 < n := by omega
    simpa [hk] using regular_of_odd_degree n k h' hne

open Filter Topology

theorem whp_of_all_regular (d : ℕ) (P : ∀ n, SimpleGraph (Fin n) → Prop)
    (hP : ∀ n (G : SimpleGraph (Fin n)), G.IsRegularOfDegree d → P n G) :
    PottsRapidMixing.WithHighProb d P := by
  classical
  unfold PottsRapidMixing.WithHighProb
  have heq : (fun n : ℕ => PottsRapidMixing.regularProb n d (P n)) =ᶠ[
      atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}] fun _ => (1 : ℝ) := by
    have hlarge : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}, d < n :=
      Filter.Eventually.filter_mono inf_le_left (eventually_gt_atTop d)
    have heven : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}, Even (n*d) :=
      Filter.Eventually.filter_mono inf_le_right (Filter.mem_principal_self _)
    filter_upwards [hlarge, heven] with n hn he
    obtain ⟨G,hG⟩ := exists_regular_graph_of_even_mul n d hn he
    have hmem : G ∈ PottsRapidMixing.regularGraphs n d := by
      simp [PottsRapidMixing.regularGraphs, hG]
    have hcard : (PottsRapidMixing.regularGraphs n d).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨G,hmem⟩
    have hfilter : (PottsRapidMixing.regularGraphs n d).filter (P n) =
        PottsRapidMixing.regularGraphs n d := by
      apply Finset.filter_eq_self.mpr
      intro H hH
      apply hP n H
      simpa [PottsRapidMixing.regularGraphs] using hH
    simp [PottsRapidMixing.regularProb, hfilter, hcard]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds


set_option autoImplicit false
open Set Metric Filter Topology
open scoped Classical
open ZeroFreeRRG.Hardcore

private theorem lam_continuous_zero (d : ℕ) : ContinuousAt (lam d) 0 := by
  unfold lam
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp

private theorem lam_zero (d : ℕ) : lam d 0 = 0 := by simp [lam]

/-- The deterministic endpoint neighborhood supplied by Lemma 5.7. -/
theorem endpoint_deterministic (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    ∃ U : Set ℂ, IsOpen U ∧ ((m.indepEndpoint : ℝ) : ℂ) ∈ U ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ v, G.degree v ≤ d) →
        ∀ z ∈ U, m.Zgraph d G z ≠ 0 := by
  cases m with
  | hardcore =>
    let R : ℝ := ((d : ℝ) - 1) ^ (d - 1) / (d : ℝ) ^ d
    have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
    have hnum : (0:ℝ) < (d:ℝ) - 1 := by linarith
    have hR : 0 < R := by dsimp [R]; positivity
    have hnear : {z : ℂ | ‖lam d z‖ < R} ∈ 𝓝 (0 : ℂ) := by
      change ∀ᶠ z in 𝓝 (0 : ℂ), ‖lam d z‖ < R
      have hc : Tendsto (lam d) (𝓝 0) (𝓝 0) := by simpa [lam_zero] using (lam_continuous_zero d).tendsto
      have h := hc.eventually (Metric.ball_mem_nhds (0 : ℂ) hR)
      simpa [Metric.mem_ball, dist_eq_norm] using h
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨Metric.ball 0 η, Metric.isOpen_ball, ?_, ?_⟩
    · simpa [Model.indepEndpoint, Metric.mem_ball] using hη
    · intro n G hG z hz
      have hlam : ‖lam d z‖ < R := hball hz
      change hardcoreZ d G z ≠ 0
      unfold hardcoreZ
      exact (lemma_5_7 d hd).1 (Fin n) G hG (lam d z) hlam
  | potts q =>
    have hq : 2 ≤ q := hm
    have hd' : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hR : 0 < (0.35:ℝ) / d := by positivity
    refine ⟨Metric.ball 1 ((0.35:ℝ)/d), Metric.isOpen_ball, ?_, ?_⟩
    · simpa [Model.indepEndpoint, Metric.mem_ball] using hR
    · intro n G hG z hz
      change pottsZ q G z ≠ 0
      apply (lemma_5_7 d hd).2 q hq (Fin n) G hG z
      simpa [Metric.mem_ball, dist_eq_norm] using hz


theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    ∃ U : Set ℂ, IsOpen U ∧ ((m.indepEndpoint : ℝ) : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0) := by
  obtain ⟨U,ho,he,hzero⟩ := endpoint_deterministic m hm d hd
  refine ⟨U,ho,he,whp_of_all_regular d _ ?_⟩
  intro n G hG z hz
  apply hzero n G (fun v => ?_) z hz
  exact le_of_eq (hG v)
