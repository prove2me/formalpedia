-- Prove2me | solution 1 for PriceOfStability.Harmonic.price_of_stability_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:21:07.691239+00:00
-- url     : https://prove2.me/submissions/fcefa568-4e9f-43fe-a27d-9c61fb27fb80

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_fig11

open CongestionPoA.AsymSum


namespace PriceOfStability.Harmonic

lemma load_split {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (e : E) :
    (load A e : ℝ) = (if e ∈ A i then 1 else 0) +
      ∑ j ∈ ({i}ᶜ : Finset ι), (if e ∈ A j then (1:ℝ) else 0) := by
  unfold load
  rw [Finset.card_filter]
  push_cast
  rw [← Fintype.sum_eq_add_sum_compl i (fun j => if e ∈ A j then (1:ℝ) else 0)]

lemma load_update_rel {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (S : ι → Finset E) (i : ι) (T : Finset E) (e : E) :
    (load (Function.update S i T) e : ℝ) + (if e ∈ S i then 1 else 0) =
      (load S e : ℝ) + (if e ∈ T then 1 else 0) := by
  rw [load_split (Function.update S i T) i e, load_split S i e]
  have : ∑ j ∈ ({i}ᶜ : Finset ι), (if e ∈ Function.update S i T j then (1:ℝ) else 0)
      = ∑ j ∈ ({i}ᶜ : Finset ι), (if e ∈ S j then (1:ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have : j ≠ i := by simpa using hj
    rw [Function.update_of_ne this]
  rw [this]
  simp only [Function.update_self]
  ring

lemma rpc_core {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S : ι → Finset E) (i : ι) (T : Finset E) :
    potential G (Function.update S i T) - potential G S =
      cost G (Function.update S i T) i - cost G S i := by
  unfold potential cost
  simp only [Function.update_self]
  rw [← Finset.sum_sub_distrib]
  have key : ∀ e, (∑ x ∈ Finset.Icc 1 (load (Function.update S i T) e), G.latency e x)
      - ∑ x ∈ Finset.Icc 1 (load S e), G.latency e x
      = (if e ∈ T then G.latency e (load (Function.update S i T) e) else 0)
        - (if e ∈ S i then G.latency e (load S e) else 0) := by
    intro e
    have h := load_update_rel S i T e
    by_cases h1 : e ∈ S i <;> by_cases h2 : e ∈ T <;> simp only [h1, h2, if_true, if_false] at h ⊢
    · have : load (Function.update S i T) e = load S e := by exact_mod_cast (show ((load (Function.update S i T) e : ℕ) : ℝ) = load S e by linarith)
      rw [this]; ring
    · have : load S e = load (Function.update S i T) e + 1 := by exact_mod_cast (show ((load S e : ℕ) : ℝ) = load (Function.update S i T) e + 1 by linarith)
      rw [this, Finset.sum_Icc_succ_top (by omega)]; ring
    · have : load (Function.update S i T) e = load S e + 1 := by exact_mod_cast (show ((load (Function.update S i T) e : ℕ) : ℝ) = load S e + 1 by linarith)
      rw [this, Finset.sum_Icc_succ_top (by omega)]; ring
    · have : load (Function.update S i T) e = load S e := by exact_mod_cast (show ((load (Function.update S i T) e : ℕ) : ℝ) = load S e by linarith)
      rw [this]; ring
  rw [Finset.sum_congr rfl (fun e _ => key e), Finset.sum_sub_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter]
  simp

lemma exists_min_pot {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S₀ : ι → Finset E) (h₀ : IsProfile G S₀) :
    ∃ S, IsProfile G S ∧ ∀ P, IsProfile G P → potential G S ≤ potential G P := by
  classical
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun A => IsProfile G A))
    (potential G) ⟨S₀, by simpa using h₀⟩
  refine ⟨S, by simpa using hS, fun P hP => hmin P (by simpa using hP)⟩

lemma min_pot_nash {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S : ι → Finset E) (hS : IsProfile G S)
    (hmin : ∀ P, IsProfile G P → potential G S ≤ potential G P) : IsPureNash G S := by
  refine ⟨hS, fun i T hT => ?_⟩
  have hP : IsProfile G (Function.update S i T) := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hT
    · rw [Function.update_of_ne hj]; exact hS j
  have h1 := hmin _ hP
  have h2 := rpc_core G S i T
  linarith

lemma imr_core {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S₀ : ι → Finset E) (h₀ : IsProfile G S₀) :
    ∃ S, IsPureNash G S ∧ potential G S ≤ potential G S₀ := by
  obtain ⟨S, hS, hmin⟩ := exists_min_pot G S₀ h₀
  exact ⟨S, min_pot_nash G S hS hmin, hmin S₀ h₀⟩

lemma t31_core {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A B : ℝ) (hA : 0 ≤ A)
    (hcost : ∀ S, IsProfile G S → sumCost G S ≤ A * potential G S)
    (hpot : ∀ S, IsProfile G S → potential G S ≤ B * sumCost G S)
    (hP : ∃ P, IsProfile G P) :
    ∃ S, IsPureNash G S ∧ ∀ P, IsProfile G P → sumCost G S ≤ A * B * sumCost G P := by
  obtain ⟨P₀, hP₀⟩ := hP
  obtain ⟨S, hS, hmin⟩ := exists_min_pot G P₀ hP₀
  refine ⟨S, min_pot_nash G S hS hmin, fun P hP => ?_⟩
  have h1 := hcost S hS
  have h2 := mul_le_mul_of_nonneg_left (hmin P hP) hA
  have h3 := mul_le_mul_of_nonneg_left (hpot P hP) hA
  nlinarith

/-! concave costs -/

lemma conc_aux (f : ℕ → ℝ) (h0 : 0 ≤ f 0)
    (hd : ∀ x, f (x + 2) - f (x + 1) ≤ f (x + 1) - f x) :
    ∀ x : ℕ, (x : ℝ) * (f (x + 1) - f x) ≤ f x := by
  intro x
  induction x with
  | zero => simpa using h0
  | succ n ih =>
    have := hd n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left this hn]

lemma ratio_step (f : ℕ → ℝ) (h0 : 0 ≤ f 0)
    (hd : ∀ x, f (x + 2) - f (x + 1) ≤ f (x + 1) - f x) (x : ℕ) (hx : 1 ≤ x) :
    f (x + 1) / ((x + 1 : ℕ) : ℝ) ≤ f x / (x : ℝ) := by
  have h := conc_aux f h0 hd x
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by positivity) hxpos]
  push_cast
  nlinarith

lemma ratio_anti (f : ℕ → ℝ) (h0 : 0 ≤ f 0)
    (hd : ∀ x, f (x + 2) - f (x + 1) ≤ f (x + 1) - f x) (x : ℕ) (hx : 1 ≤ x) :
    ∀ n, x ≤ n → f n / (n : ℝ) ≤ f x / (x : ℝ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (ratio_step f h0 hd m (le_trans hx hm)).trans ih

lemma harm_mono {m n : ℕ} (h : m ≤ n) : (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  have : harmonic m ≤ harmonic n := by
    unfold harmonic
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    intro i _ _; positivity
  exact_mod_cast this

lemma harm_cast (n : ℕ) : (harmonic n : ℝ) = ∑ x ∈ Finset.Icc 1 n, (1 / (x : ℝ)) := by
  rw [harmonic_eq_sum_Icc]; push_cast; simp

lemma edge_bounds (f : ℕ → ℝ) (h0 : 0 ≤ f 0) (hm : Monotone f)
    (hd : ∀ x, f (x + 2) - f (x + 1) ≤ f (x + 1) - f x) (n : ℕ) (hn : 1 ≤ n) :
    f n ≤ ∑ x ∈ Finset.Icc 1 n, f x / (x : ℝ) ∧
      ∑ x ∈ Finset.Icc 1 n, f x / (x : ℝ) ≤ (harmonic n : ℝ) * f n := by
  constructor
  · have : ∑ x ∈ Finset.Icc 1 n, f n / (n : ℝ) ≤ ∑ x ∈ Finset.Icc 1 n, f x / (x : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Finset.mem_Icc] at hx
      exact ratio_anti f h0 hd x hx.1 n hx.2
    rw [Finset.sum_const, Nat.card_Icc] at this
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    simp only [Nat.add_sub_cancel, nsmul_eq_mul] at this
    rwa [mul_div_cancel₀ _ hnpos.ne'] at this
  · rw [harm_cast, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x hx
    rw [Finset.mem_Icc] at hx
    have hxpos : (0:ℝ) < x := by exact_mod_cast hx.1
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (hm hx.2) hxpos.le

lemma load_le_card {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (S : ι → Finset E) (e : E) : load S e ≤ Fintype.card ι := by
  unfold load
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma pot_eq_filter {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (S : ι → Finset E) :
    potential G S = ∑ e ∈ Finset.univ.filter (fun e => 0 < load S e),
      ∑ x ∈ Finset.Icc 1 (load S e), G.latency e x := by
  unfold potential
  rw [Finset.sum_filter_of_ne]
  intro e _ hne
  by_contra h
  apply hne
  have : load S e = 0 := by omega
  rw [this]; simp

lemma clp_core {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ)
    (hc : IsConcaveCost c) (S : ι → Finset E) :
    designCost c S ≤ potential (fairGame strategies c) S ∧
      potential (fairGame strategies c) S ≤ (harmonic (Fintype.card ι) : ℝ) * designCost c S := by
  rw [pot_eq_filter]
  unfold designCost
  simp only [fairGame]
  constructor
  · apply Finset.sum_le_sum
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨h0, hm, hd⟩ := hc e
    exact (edge_bounds (c e) h0 hm hd _ he.2).1
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨h0, hm, hd⟩ := hc e
    have hnn : 0 ≤ c e (load S e) := h0.trans (hm (Nat.zero_le _))
    exact (edge_bounds (c e) h0 hm hd _ he.2).2.trans
      (mul_le_mul_of_nonneg_right (harm_mono (load_le_card S e)) hnn)

lemma sumCost_fair {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) (S : ι → Finset E) :
    sumCost (fairGame strategies c) S = designCost c S := by
  unfold sumCost cost designCost
  simp only [fairGame]
  have : ∀ i, ∑ e ∈ S i, c e (load S e) / (load S e : ℝ)
      = ∑ e, if e ∈ S i then c e (load S e) / (load S e : ℝ) else 0 := by
    intro i; rw [← Finset.sum_filter]; simp
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_comm]
  rw [← Finset.sum_filter_of_ne (p := fun e => 0 < load S e)]
  · apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.univ.filter (fun i => e ∈ S i)).card : ℝ) = load S e := rfl
    rw [this]
    have hpos : (0:ℝ) < load S e := by exact_mod_cast he.2
    field_simp
  · intro e _ hne
    by_contra h
    apply hne
    have : load S e = 0 := by omega
    simp [this]

lemma t23_core {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) (hc : IsConcaveCost c)
    (hP : ∃ P, IsProfile (fairGame strategies c) P) :
    ∃ S, IsPureNash (fairGame strategies c) S ∧
      ∀ P, IsProfile (fairGame strategies c) P →
        designCost c S ≤ (harmonic (Fintype.card ι) : ℝ) * designCost c P := by
  obtain ⟨S, hS, h⟩ := t31_core (fairGame strategies c) 1 (harmonic (Fintype.card ι) : ℝ) zero_le_one
    (fun S _ => by rw [sumCost_fair, one_mul]; exact (clp_core strategies c hc S).1)
    (fun S _ => by rw [sumCost_fair]; exact (clp_core strategies c hc S).2) hP
  refine ⟨S, hS, fun P hP => ?_⟩
  have := h P hP
  rw [sumCost_fair, sumCost_fair, one_mul] at this
  exact this



lemma load_pos_iff' {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) : 0 < load A e ↔ ∃ j, e ∈ A j := by
  unfold load
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp

lemma load_eq_one' {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) (i : ι) (hi : e ∈ A i) (hj : ∀ j, j ≠ i → e ∉ A j) :
    load A e = 1 := by
  unfold load
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; by_contra hne; exact hj j hne h
  · rintro rfl; exact hi

lemma fig_strat {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (hS : IsProfile (fig11 k ε) S)
    (j : Fin k) : S j = {Fig11Edge.own j} ∨ S j = {Fig11Edge.common, Fig11Edge.zero j} := by
  have := hS j
  simpa [fig11, fairGame, fig11Strategies] using this

lemma own_not_mem {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (hS : IsProfile (fig11 k ε) S)
    (i j : Fin k) (h : j ≠ i) : Fig11Edge.own i ∉ S j := by
  rcases fig_strat S hS j with h1 | h1 <;> rw [h1] <;> simp [Ne.symm h]

lemma fig_latency (k : ℕ) (ε : ℝ) (e : Fig11Edge k) (x : ℕ) :
    (fig11 k ε).latency e x = fig11Cost k ε e / x := rfl

lemma fig_strat_mem (k : ℕ) (ε : ℝ) (i : Fin k) :
    {Fig11Edge.own i} ∈ (fig11 k ε).strategies i ∧
      {Fig11Edge.common, Fig11Edge.zero i} ∈ (fig11 k ε).strategies i := by
  simp [fig11, fairGame, fig11Strategies]

lemma cost_own {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (hS : IsProfile (fig11 k ε) S)
    (i : Fin k) (hi : S i = {Fig11Edge.own i}) :
    cost (fig11 k ε) S i = 1 / ((i : ℕ) + 1 : ℝ) := by
  unfold cost
  rw [hi, Finset.sum_singleton, fig_latency,
    load_eq_one' S _ i (by rw [hi]; simp) (fun j hj => own_not_mem S hS i j hj)]
  simp [fig11Cost]

lemma cost_common {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (i : Fin k)
    (hi : S i = {Fig11Edge.common, Fig11Edge.zero i}) :
    cost (fig11 k ε) S i = (1 + ε) / (load S Fig11Edge.common : ℝ) := by
  unfold cost
  rw [hi, Finset.sum_pair (by simp), fig_latency, fig_latency]
  simp [fig11Cost]

lemma isProfile_update {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k))
    (hS : IsProfile (fig11 k ε) S) (i : Fin k) (T : Finset (Fig11Edge k))
    (hT : T ∈ (fig11 k ε).strategies i) : IsProfile (fig11 k ε) (Function.update S i T) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hT
  · rw [Function.update_of_ne hj]; exact hS j

def allOwn (k : ℕ) : Fin k → Finset (Fig11Edge k) := fun i => {Fig11Edge.own i}
def allCommon (k : ℕ) : Fin k → Finset (Fig11Edge k) := fun i => {Fig11Edge.common, Fig11Edge.zero i}

lemma allOwn_profile (k : ℕ) (ε : ℝ) : IsProfile (fig11 k ε) (allOwn k) :=
  fun i => (fig_strat_mem k ε i).1

lemma allCommon_profile (k : ℕ) (ε : ℝ) : IsProfile (fig11 k ε) (allCommon k) :=
  fun i => (fig_strat_mem k ε i).2

lemma allOwn_nash (k : ℕ) (ε : ℝ) (hε : 0 < ε) : IsPureNash (fig11 k ε) (allOwn k) := by
  refine ⟨allOwn_profile k ε, fun i T hT => ?_⟩
  have hP := isProfile_update _ (allOwn_profile k ε) i T hT
  rw [cost_own _ (allOwn_profile k ε) i rfl]
  rcases fig_strat _ hP i with h | h
  · rw [cost_own _ hP i h]
  · rw [Function.update_self] at h
    rw [cost_common _ i (by rw [Function.update_self]; exact h)]
    rw [load_eq_one' _ _ i (by rw [Function.update_self, h]; simp)]
    · have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      simp only [Nat.cast_one]
      nlinarith
    · intro j hj
      rw [Function.update_of_ne hj]
      simp [allOwn]

lemma nash_eq_allOwn (k : ℕ) (ε : ℝ) (hε : 0 < ε) (S : Fin k → Finset (Fig11Edge k))
    (hS : IsPureNash (fig11 k ε) S) : S = allOwn k := by
  classical
  obtain ⟨hprof, hnash⟩ := hS
  set U := Finset.univ.filter (fun j => Fig11Edge.common ∈ S j) with hU
  by_cases hne : U.Nonempty
  · exfalso
    set i := U.max' hne
    have hiU : i ∈ U := U.max'_mem hne
    have hci : Fig11Edge.common ∈ S i := by simpa [hU] using hiU
    have hSi : S i = {Fig11Edge.common, Fig11Edge.zero i} := by
      rcases fig_strat S hprof i with h | h
      · rw [h] at hci; simp at hci
      · exact h
    have hm : load S Fig11Edge.common = U.card := rfl
    have hsub : U ⊆ Finset.Iic i := fun j hj => Finset.mem_Iic.mpr (U.le_max' j hj)
    have hcard : U.card ≤ (i:ℕ) + 1 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hpos : 1 ≤ U.card := Finset.card_pos.mpr hne
    have h1 := hnash i {Fig11Edge.own i} (fig_strat_mem k ε i).1
    have hP := isProfile_update S hprof i _ (fig_strat_mem k ε i).1
    rw [cost_own _ hP i (by simp), cost_common S i hSi, hm] at h1
    have hmR : (1:ℝ) ≤ U.card := by exact_mod_cast hpos
    have hcR : (U.card:ℝ) ≤ (i:ℕ) + 1 := by exact_mod_cast hcard
    rw [div_le_div_iff₀ (by linarith) (by positivity)] at h1
    nlinarith
  · funext j
    rcases fig_strat S hprof j with h | h
    · exact h
    · exfalso; apply hne; exact ⟨j, by simp [hU, h]⟩

def ownEmb (k : ℕ) : Fin k ↪ Fig11Edge k := ⟨Fig11Edge.own, fun a b h => by cases h; rfl⟩
def zeroEmb (k : ℕ) : Fin k ↪ Fig11Edge k := ⟨Fig11Edge.zero, fun a b h => by cases h; rfl⟩
@[simp] lemma ownEmb_apply (k : ℕ) (a : Fin k) : ownEmb k a = Fig11Edge.own a := rfl
@[simp] lemma zeroEmb_apply (k : ℕ) (a : Fin k) : zeroEmb k a = Fig11Edge.zero a := rfl

lemma design_allOwn (k : ℕ) (ε : ℝ) :
    designCost (fun e _ => fig11Cost k ε e) (allOwn k) = (harmonic k : ℝ) := by
  unfold designCost
  have : Finset.univ.filter (fun e => 0 < load (allOwn k) e)
      = Finset.univ.map (ownEmb k) := by
    ext e
    cases e <;> simp [load_pos_iff', allOwn, ownEmb_apply, zeroEmb_apply]
  rw [this, Finset.sum_map]
  simp only [ownEmb_apply, fig11Cost]
  unfold harmonic
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun i => 1 / ((i:ℝ) + 1))]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma design_allCommon (k : ℕ) (ε : ℝ) (hk : 1 ≤ k) :
    designCost (fun e _ => fig11Cost k ε e) (allCommon k) = 1 + ε := by
  unfold designCost
  have : Finset.univ.filter (fun e => 0 < load (allCommon k) e)
      = insert Fig11Edge.common (Finset.univ.map (zeroEmb k)) := by
    ext e
    cases e <;> simp [load_pos_iff', allCommon, ownEmb_apply, zeroEmb_apply]
    exact ⟨⟨0, hk⟩⟩
  rw [this, Finset.sum_insert (by simp), Finset.sum_map]
  simp [fig11Cost]

lemma fig_core (k : ℕ) (ε : ℝ) (hk : 1 ≤ k) (hε : 0 < ε) :
    (∃! S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε := by
  refine ⟨⟨allOwn k, allOwn_nash k ε hε, fun S hS => nash_eq_allOwn k ε hε S hS⟩, ?_, ?_⟩
  · intro S hS
    rw [nash_eq_allOwn k ε hε S hS, design_allOwn]
  · exact ⟨allCommon k, allCommon_profile k ε, design_allCommon k ε hk⟩


theorem posh_core :
    (∀ {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
      (strategies : ι → Finset (Finset E)) (c : E → ℝ), (∀ e, 0 ≤ c e) →
      (∃ P, IsProfile (fairGame strategies (fun e _ => c e)) P) →
      ∃ S, IsPureNash (fairGame strategies (fun e _ => c e)) S ∧
        ∀ P, IsProfile (fairGame strategies (fun e _ => c e)) P →
          designCost (fun e _ => c e) S ≤
            (harmonic (Fintype.card ι) : ℝ) * designCost (fun e _ => c e) P) ∧
    (∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε →
      (∃ S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε) := by
  refine ⟨?_, ?_⟩
  · intro ι E _ _ _ _ strategies c hc hP
    apply t23_core strategies (fun e _ => c e) _ hP
    intro e
    exact ⟨hc e, fun _ _ _ => le_rfl, fun _ => by simp⟩
  · intro k ε hk hε
    obtain ⟨h1, h2, h3⟩ := fig_core k ε hk hε
    exact ⟨h1.exists, h2, h3⟩

end PriceOfStability.Harmonic

open PriceOfStability.Harmonic
open CongestionPoA.AsymSum

theorem solution :
    (∀ {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
      (strategies : ι → Finset (Finset E)) (c : E → ℝ), (∀ e, 0 ≤ c e) →
      (∃ P, IsProfile (fairGame strategies (fun e _ => c e)) P) →
      ∃ S, IsPureNash (fairGame strategies (fun e _ => c e)) S ∧
        ∀ P, IsProfile (fairGame strategies (fun e _ => c e)) P →
          designCost (fun e _ => c e) S ≤
            (harmonic (Fintype.card ι) : ℝ) * designCost (fun e _ => c e) P) ∧
    (∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε →
      (∃ S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε) := by
  exact posh_core
