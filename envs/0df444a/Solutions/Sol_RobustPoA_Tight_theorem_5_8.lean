-- Prove2me | solution 1 for RobustPoA.Tight.theorem_5_8
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T06:59:16.252348+00:00
-- url     : https://prove2.me/submissions/d204e3d2-3298-4ded-9ac5-0f9b1fc8ae38

import Definitions.Def_RobustPoA_Tight_Classes
open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof
end PoATightProof

open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

omit [DecidableEq ι] [Fintype E] in
theorem load_pos {A : ι → Finset E} {i : ι} {e : E} (he : e ∈ A i) :
    1 ≤ load A e := by
  exact Finset.card_pos.mpr ⟨i, by simp [he]⟩

omit [DecidableEq ι] [Fintype E] in
theorem cost_nonneg {C : Set (ℕ → ℝ)} (hC : ∀ c ∈ C, IsCostFn c)
    (G : CongestionGame ι E) (hc : ∀ e, G.latency e ∈ C) (A : ι → Finset E) (i : ι) :
    0 ≤ cost G A i := by
  exact Finset.sum_nonneg fun e he => (hC _ (hc e)).1 _ (load_pos he)

omit [DecidableEq ι] [Fintype E] in
theorem sumCost_nonneg {C : Set (ℕ → ℝ)} (hC : ∀ c ∈ C, IsCostFn c)
    (G : CongestionGame ι E) (hc : ∀ e, G.latency e ∈ C) (A : ι → Finset E) :
    0 ≤ sumCost G A := Finset.sum_nonneg fun i _ => cost_nonneg hC G hc A i

omit [DecidableEq ι] in
theorem sumCost_eq_resource_sum (G : CongestionGame ι E) (A : ι → Finset E) :
    sumCost G A = ∑ e, G.latency e (load A e) * (load A e : ℝ) := by
  have hh : sumCost G A = ∑ i, ∑ e, if e ∈ A i then G.latency e (load A e) else 0 := by
    unfold sumCost cost
    congr 1
    funext i
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp
  rw [hh, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_filter]
  simp [load, mul_comm]

omit [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] in
theorem exists_profile (G : CongestionGame ι E) (hn : ∀ i, (G.strategies i).Nonempty) :
    ∃ A, IsProfile G A := by
  choose A hA using hn
  exact ⟨A, hA⟩

theorem exists_opt_profile (G : CongestionGame ι E)
    (hn : ∀ i, (G.strategies i).Nonempty) :
    ∃ A, IsProfile G A ∧ optCost G = ENNReal.ofReal (sumCost G A) := by
  obtain ⟨A, hA⟩ := exists_profile G hn
  let s : Finset (ι → Finset E) := Finset.univ.filter (IsProfile G)
  have hs : s.Nonempty := ⟨A, by simp [s, hA]⟩
  obtain ⟨B, hB, hmin⟩ := s.exists_min_image (fun A => ENNReal.ofReal (sumCost G A)) hs
  have hBP : IsProfile G B := (Finset.mem_filter.mp hB).2
  refine ⟨B, hBP, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le B (iInf_le_of_le hBP le_rfl)
  · refine le_iInf fun A => le_iInf fun hA => ?_
    exact hmin A (by simp [s, hA])

theorem optCost_le (G : CongestionGame ι E) {A : ι → Finset E} (hA : IsProfile G A) :
    optCost G ≤ ENNReal.ofReal (sumCost G A) :=
  iInf_le_of_le A (iInf_le_of_le hA le_rfl)

theorem nash_ratio_le_worst {C : Set (ℕ → ℝ)} {k m : ℕ}
    (G : CongestionGame (Fin k) (Fin m)) (hG : InClass C G)
    {A : Fin k → Finset (Fin m)} (hA : IsPureNash G A) :
    ENNReal.ofReal (sumCost G A) / optCost G ≤ worstPoA C := by
  exact le_iSup_of_le k (le_iSup_of_le m (le_iSup_of_le G
    (le_iSup_of_le hG (le_iSup_of_le A (le_iSup_of_le hA le_rfl)))))

theorem nash_cost_le_worst_mul {C : Set (ℕ → ℝ)}
    (hC : ∀ c ∈ C, IsCostFn c) (hW : worstPoA C ≠ ⊤) {k m : ℕ}
    (G : CongestionGame (Fin k) (Fin m)) (hG : InClass C G)
    {A B : Fin k → Finset (Fin m)} (hA : IsPureNash G A) (hB : IsProfile G B) :
    sumCost G A ≤ (worstPoA C).toReal * sumCost G B := by
  have ho : optCost G ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (optCost_le G hB)
  have hh := (ENNReal.div_le_iff_le_mul (Or.inr hW) (Or.inl ho)).mp
    (nash_ratio_le_worst G hG hA)
  have hh' : ENNReal.ofReal (sumCost G A) ≤ worstPoA C * ENNReal.ofReal (sumCost G B) :=
    hh.trans (by gcongr; exact optCost_le G hB)
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top hW ENNReal.ofReal_ne_top) hh'
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sumCost_nonneg hC G hG.1 A),
    ENNReal.toReal_ofReal (sumCost_nonneg hC G hG.1 B)] using this

end PoATightProof

open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof
variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

noncomputable def mapProfile (e : E ≃ F) (A : ι → Finset E) : ι → Finset F :=
  fun i => (A i).map e.toEmbedding

noncomputable def reindexGame (e : E ≃ F) (G : CongestionGame ι E) : CongestionGame ι F where
  strategies i := (G.strategies i).image (fun s => s.map e.toEmbedding)
  latency f := G.latency (e.symm f)

omit [DecidableEq ι] [Fintype E] [Fintype F] in
theorem load_map (e : E ≃ F) (A : ι → Finset E) (f : F) :
    load (mapProfile e A) f = load A (e.symm f) := by
  simp only [load, mapProfile, Finset.mem_map_equiv]

omit [DecidableEq ι] [Fintype E] [Fintype F] in
theorem cost_map (e : E ≃ F) (G : CongestionGame ι E) (A : ι → Finset E) (i : ι) :
    cost (reindexGame e G) (mapProfile e A) i = cost G A i := by
  simp [cost, mapProfile, reindexGame, Finset.sum_map, load_map]

omit [DecidableEq ι] [Fintype E] [Fintype F] in
theorem sumCost_map (e : E ≃ F) (G : CongestionGame ι E) (A : ι → Finset E) :
    sumCost (reindexGame e G) (mapProfile e A) = sumCost G A := by
  simp only [sumCost, cost_map]

omit [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] [Fintype F] in
theorem profile_map (e : E ≃ F) (G : CongestionGame ι E) {A : ι → Finset E}
    (hA : IsProfile G A) : IsProfile (reindexGame e G) (mapProfile e A) := by
  intro i
  exact Finset.mem_image.mpr ⟨A i, hA i, rfl⟩

omit [Fintype ι] [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] in
theorem map_update (e : E ≃ F) (A : ι → Finset E) (i : ι) (s : Finset E) :
    mapProfile e (Function.update A i s) =
      Function.update (mapProfile e A) i (s.map e.toEmbedding) := by
  funext j
  by_cases h : j = i <;> simp [mapProfile, h]

omit [Fintype E] [Fintype F] in
theorem nash_map (e : E ≃ F) (G : CongestionGame ι E) {A : ι → Finset E}
    (hA : IsPureNash G A) : IsPureNash (reindexGame e G) (mapProfile e A) := by
  refine ⟨profile_map e G hA.1, ?_⟩
  intro i s hs
  change s ∈ (G.strategies i).image (fun t => t.map e.toEmbedding) at hs
  obtain ⟨s, hs0, rfl⟩ := Finset.mem_image.mp hs
  rw [← map_update, cost_map, cost_map]
  exact hA.2 i s hs0

omit [DecidableEq E] in
theorem reindex_inClass {C : Set (ℕ → ℝ)} {k : ℕ}
    (G : CongestionGame (Fin k) E) (hc : ∀ e, G.latency e ∈ C)
    (hn : ∀ i, (G.strategies i).Nonempty) :
    InClass C (reindexGame (Fintype.equivFin E) G) := by
  refine ⟨fun _ => hc _, fun i => ?_⟩
  obtain ⟨s, hs⟩ := hn i
  exact ⟨_, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩

end PoATightProof

open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof
variable {T : Type*} [Fintype T] [DecidableEq T] {k : ℕ} [NeZero k]

noncomputable def cycleProfile (P : T → Finset (Fin k)) (i : Fin k) : Finset (T × Fin k) :=
  Finset.univ.filter fun e => e.2 - i ∈ P e.1

omit [DecidableEq T] [NeZero k] in
theorem mem_cycleProfile (P : T → Finset (Fin k)) (i : Fin k) (e : T × Fin k) :
    e ∈ cycleProfile P i ↔ e.2 - i ∈ P e.1 := by simp [cycleProfile]

theorem card_left_sub_filter (s : Finset (Fin k)) (v : Fin k) :
    (Finset.univ.filter fun i => v - i ∈ s).card = s.card := by
  apply Finset.card_bij (fun i _ => v - i)
  · simp
  · intro a ha b hb h
    exact sub_right_injective h
  · intro b hb
    exact ⟨v - b, by simpa using hb, by simp⟩

theorem card_right_sub_filter (s : Finset (Fin k)) (i : Fin k) :
    (Finset.univ.filter fun v => v - i ∈ s).card = s.card := by
  apply Finset.card_bij (fun v _ => v - i)
  · simp
  · intro a ha b hb h
    exact sub_left_injective h
  · intro b hb
    exact ⟨b + i, by simpa using hb, by simp⟩

theorem load_cycle (P : T → Finset (Fin k)) (e : T × Fin k) :
    load (cycleProfile P) e = (P e.1).card := by
  simp only [load, mem_cycleProfile]
  exact card_left_sub_filter _ _

noncomputable def cycleGame (c : T → ℕ → ℝ) (P Q : T → Finset (Fin k)) :
    CongestionGame (Fin k) (T × Fin k) where
  strategies i := {cycleProfile P i, cycleProfile Q i}
  latency e := c e.1

omit [NeZero k] in
theorem cycle_profile (c : T → ℕ → ℝ) (P Q : T → Finset (Fin k)) :
    IsProfile (cycleGame c P Q) (cycleProfile P) ∧
      IsProfile (cycleGame c P Q) (cycleProfile Q) := by
  constructor <;> intro i <;> simp [cycleGame]

theorem cycle_cost (c : T → ℕ → ℝ) (P Q : T → Finset (Fin k))
    (R : T → Finset (Fin k)) (i : Fin k) :
    cost (cycleGame c P Q) (cycleProfile R) i =
      ∑ t, c t (R t).card * ((R t).card : ℝ) := by
  unfold cost
  simp only [cycleProfile, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  congr 1
  funext t
  simp only [cycleGame]
  have hl (v : Fin k) : load (cycleProfile R) (t,v) = (R t).card := load_cycle _ _
  simp only [hl]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, card_right_sub_filter]
  ring

theorem load_update_new {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (A : ι → Finset E) (i : ι) (s : Finset E) (e : E)
    (he : e ∈ s) (hn : e ∉ A i) :
    load (Function.update A i s) e = load A e + 1 := by
  have hh : Finset.univ.filter (fun j => e ∈ Function.update A i s j) =
      insert i (Finset.univ.filter fun j => e ∈ A j) := by
    ext j
    by_cases h : j = i <;> simp [h, he, Function.update_apply]
  simp only [load, hh]
  rw [Finset.card_insert_of_notMem (by simpa using hn)]

theorem cycle_deviation_cost (c : T → ℕ → ℝ) (P Q : T → Finset (Fin k))
    (hd : ∀ t, Disjoint (P t) (Q t)) (i : Fin k) :
    cost (cycleGame c P Q) (Function.update (cycleProfile P) i (cycleProfile Q i)) i =
      ∑ t, c t ((P t).card + 1) * ((Q t).card : ℝ) := by
  have hh (e : T × Fin k) (he : e ∈ cycleProfile Q i) :
      load (Function.update (cycleProfile P) i (cycleProfile Q i)) e = (P e.1).card + 1 := by
    rw [load_update_new _ _ _ _ he, load_cycle]
    intro h
    exact Finset.disjoint_left.mp (hd e.1) (mem_cycleProfile _ _ _ |>.mp h)
      (mem_cycleProfile _ _ _ |>.mp he)
  unfold cost
  rw [Function.update_self]
  change (∑ e ∈ cycleProfile Q i, c e.1 (load (Function.update (cycleProfile P) i (cycleProfile Q i)) e)) = _
  rw [Finset.sum_congr rfl (fun e he => congrArg (c e.1) (hh e he))]
  simp only [cycleProfile, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  congr 1
  funext t
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, card_right_sub_filter]
  ring

theorem cycle_nash (c : T → ℕ → ℝ) (P Q : T → Finset (Fin k))
    (hd : ∀ t, Disjoint (P t) (Q t))
    (h : (∑ t, c t (P t).card * ((P t).card : ℝ)) ≤
      ∑ t, c t ((P t).card + 1) * ((Q t).card : ℝ)) :
    IsPureNash (cycleGame c P Q) (cycleProfile P) := by
  refine ⟨(cycle_profile c P Q).1, ?_⟩
  intro i s hs
  simp only [cycleGame, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · simp
  · rw [cycle_cost, cycle_deviation_cost c P Q hd]
    exact h

end PoATightProof

open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof

theorem finite_witness_bound {C : Set (ℕ → ℝ)}
    (hC : ∀ c ∈ C, IsCostFn c) (hW : worstPoA C ≠ ⊤)
    {T : Type*} [Fintype T] [DecidableEq T]
    (c : T → ℕ → ℝ) (x y : T → ℕ) (hc : ∀ t, c t ∈ C) (_hy : ∀ t, 1 ≤ y t)
    (hbalance : (∑ t, c t (x t) * (x t : ℝ)) ≤
      ∑ t, c t (x t + 1) * (y t : ℝ)) :
    (∑ t, c t (x t) * (x t : ℝ)) ≤
      (worstPoA C).toReal * ∑ t, c t (y t) * (y t : ℝ) := by
  let k := (Finset.univ.sup fun t => x t + y t) + 1
  have hk : 0 < k := Nat.succ_pos _
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hxy (t : T) : x t + y t < k :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun t => x t + y t) (Finset.mem_univ t))
  have hx (t : T) : x t < k := by have := hxy t; omega
  let P : T → Finset (Fin k) := fun t => Finset.Iio ⟨x t, hx t⟩
  let Q : T → Finset (Fin k) := fun t => Finset.Ico ⟨x t, hx t⟩ ⟨x t + y t, hxy t⟩
  have hp (t : T) : (P t).card = x t := by simp [P]
  have hq (t : T) : (Q t).card = y t := by simp [Q]
  have hd (t : T) : Disjoint (P t) (Q t) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [P, Q, Finset.mem_Iio, Finset.mem_Ico] at ha hb
    exact (not_lt_of_ge hb.1) ha
  let G := cycleGame c P Q
  have hG : InClass C (reindexGame (Fintype.equivFin (T × Fin k)) G) :=
    reindex_inClass G (fun e => hc e.1) (fun i => ⟨cycleProfile P i, by simp [G, cycleGame]⟩)
  have hn : IsPureNash G (cycleProfile P) := by
    apply cycle_nash c P Q hd
    simpa only [hp, hq] using hbalance
  have hb : IsProfile G (cycleProfile Q) := (cycle_profile c P Q).2
  have hh := nash_cost_le_worst_mul hC hW _ hG
    (nash_map (Fintype.equivFin (T × Fin k)) G hn)
    (profile_map (Fintype.equivFin (T × Fin k)) G hb)
  simp only [sumCost_map] at hh
  have ha : sumCost G (cycleProfile P) = (k : ℝ) * ∑ t, c t (x t) * (x t : ℝ) := by
    simp [sumCost, G, cycle_cost, hp]
  have hb' : sumCost G (cycleProfile Q) = (k : ℝ) * ∑ t, c t (y t) * (y t : ℝ) := by
    simp [sumCost, G, cycle_cost, hq]
  rw [ha, hb'] at hh
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  nlinarith

end PoATightProof

open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof

/-- Integer multiplicities detect a strict violation at the balanced real ratio. -/
theorem balanced_of_nat (e₁ e₂ b₁ b₂ : ℝ) (he₁ : e₁ < 0) (he₂ : 0 < e₂)
    (h : ∀ m n : ℕ, 0 ≤ (m : ℝ) * e₁ + (n : ℝ) * e₂ →
      (m : ℝ) * b₁ + (n : ℝ) * b₂ ≤ 0) :
    e₂ * b₁ - e₁ * b₂ ≤ 0 := by
  by_contra hfail
  have hfail' : 0 < e₂ * b₁ - e₁ * b₂ := lt_of_not_ge hfail
  let r : ℝ := -e₁ / e₂
  have hr : 0 < r := div_pos (neg_pos.mpr he₁) he₂
  have hre : r * e₂ = -e₁ := by dsimp [r]; field_simp
  have hscale : e₂ * (b₁ + r * b₂) = e₂ * b₁ - e₁ * b₂ := by
    calc
      _ = e₂ * b₁ + (r * e₂) * b₂ := by ring
      _ = _ := by rw [hre]; ring
  have hval : 0 < b₁ + r * b₂ := by
    apply (mul_pos_iff_of_pos_left he₂).mp
    rwa [hscale]
  let ε : ℝ := (b₁ + r * b₂) / (|b₂| + 1)
  have habs : 0 < |b₂| + 1 := by positivity
  have hε : 0 < ε := div_pos hval habs
  have hεeq : ε * (|b₂| + 1) = b₁ + r * b₂ := by dsimp [ε]; field_simp
  obtain ⟨m, hm⟩ := exists_nat_gt ε⁻¹
  have hmpos : 0 < (m : ℝ) := (inv_pos.mpr hε).trans hm
  obtain ⟨z, hzlo, hzhi⟩ := exists_div_btwn (show r < r + ε by linarith)
    (show ((r + ε) - r)⁻¹ < (m : ℝ) by simpa using hm)
  have hzpos : 0 < (z : ℝ) := (div_pos_iff.mp (hr.trans hzlo)).elim
    (fun hz => hz.1) (fun hz => False.elim (not_lt_of_ge hmpos.le hz.2))
  have hznonneg : 0 ≤ z := by exact_mod_cast hzpos.le
  let n : ℕ := z.toNat
  have hn : (n : ℝ) = (z : ℝ) := by
    dsimp [n]
    exact_mod_cast (Int.toNat_of_nonneg hznonneg)
  have hδ : 0 < (z : ℝ) / m - r := sub_pos.mpr hzlo
  have hδlt : (z : ℝ) / m - r < ε := by linarith
  have hprod := mul_le_mul_of_nonneg_left (neg_abs_le b₂) hδ.le
  have hsmall := mul_lt_mul_of_pos_right hδlt habs
  have hpositive : 0 < b₁ + ((z : ℝ) / m) * b₂ := by nlinarith
  have he : 0 ≤ (m : ℝ) * e₁ + (n : ℝ) * e₂ := by
    rw [hn]
    have hz : r * (m : ℝ) < (z : ℝ) := (lt_div_iff₀ hmpos).mp hzlo
    nlinarith
  have hh := h m n he
  rw [hn] at hh
  have hclear : (m : ℝ) * (b₁ + ((z : ℝ) / m) * b₂) =
      (m : ℝ) * b₁ + (z : ℝ) * b₂ := by field_simp
  nlinarith [mul_pos hmpos hpositive]

/-- A positive lower endpoint and pairwise compatibility yield a positive common point. -/
theorem interval_common_point {ι : Type*} (A B E : ι → ℝ) (q : ℝ)
    (hzero : ∀ i, E i = 0 → B i ≤ q * A i)
    (hpair : ∀ i j, E i < 0 → 0 < E j →
      (B i - q * A i) / (-E i) ≤ (q * A j - B j) / E j)
    (hupper : ∃ j, 0 < E j)
    (hpositive : ∃ i, E i < 0 ∧ 0 < (B i - q * A i) / (-E i)) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, B i + t * E i ≤ q * A i := by
  let S : Set ℝ := {l | ∃ i, E i < 0 ∧ l = (B i - q * A i) / (-E i)}
  obtain ⟨i₀, hi₀, hp⟩ := hpositive
  have hmem : (B i₀ - q * A i₀) / (-E i₀) ∈ S := ⟨i₀, hi₀, rfl⟩
  have hne : S.Nonempty := ⟨_, hmem⟩
  obtain ⟨j₀, hj₀⟩ := hupper
  have hbd : BddAbove S := by
    refine ⟨(q * A j₀ - B j₀) / E j₀, ?_⟩
    rintro l ⟨i, hi, rfl⟩
    exact hpair i j₀ hi hj₀
  refine ⟨sSup S, hp.trans_le (le_csSup hbd hmem), ?_⟩
  intro i
  rcases lt_trichotomy (E i) 0 with hi | hi | hi
  · have hle := le_csSup hbd (show (B i - q * A i) / (-E i) ∈ S from ⟨i, hi, rfl⟩)
    have := (div_le_iff₀ (neg_pos.mpr hi)).mp hle
    nlinarith
  · simpa [hi] using hzero i hi
  · have hle : sSup S ≤ (q * A i - B i) / E i := by
      apply csSup_le hne
      rintro l ⟨j, hj, rfl⟩
      exact hpair j i hj hi
    have := (le_div_iff₀ hi).mp hle
    linarith

end PoATightProof

open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof

theorem cost_mass_nonneg {c : ℕ → ℝ} (hc : IsCostFn c) (x : ℕ) :
    0 ≤ c x * (x : ℝ) := by
  by_cases hx : x = 0
  · simp [hx]
  · exact mul_nonneg (hc.1 x (by omega)) (Nat.cast_nonneg x)

theorem resource_mu_nonneg {C : Set (ℕ → ℝ)} (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) {p : ℝ × ℝ} (hp : p ∈ smoothParams C) : 0 ≤ p.2 := by
  by_contra hh
  have hμ : p.2 < 0 := lt_of_not_ge hh
  obtain ⟨c, hc⟩ := hne
  obtain ⟨y, hy, hcy⟩ := (hC c hc).2.2
  have hcypos : 0 < c y := lt_of_le_of_ne ((hC c hc).1 y hy) (Ne.symm hcy)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (y : ℝ) (p.1 * y / (-p.2)))
  have hyn : y ≤ n := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hn))
  have hnpos : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hlarge : p.1 * (y : ℝ) + p.2 * (n : ℝ) < 0 := by
    have := (div_lt_iff₀ (neg_pos.mpr hμ)).mp ((le_max_right _ _).trans_lt hn)
    nlinarith
  have hmono := (hC c hc).2.1 y n hy hyn
  have hmul := mul_le_mul_of_nonpos_left hmono (mul_nonpos_of_nonpos_of_nonneg hμ.le hnpos)
  have hineq := hp.2 c hc n y hy
  have hlhs : 0 ≤ c (n + 1) * (y : ℝ) :=
    mul_nonneg ((hC c hc).1 _ (by omega)) (Nat.cast_nonneg _)
  nlinarith [mul_neg_of_pos_of_neg hcypos hlarge]

theorem load_update_le {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) :
    load (Function.update A i S) e ≤ load A e + 1 := by
  have hs : Finset.univ.filter (fun j => e ∈ Function.update A i S j) ⊆
      insert i (Finset.univ.filter (fun j => e ∈ A j)) := by
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_insert_of_mem (by simpa [Function.update_of_ne hji] using hj)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

theorem resource_smooth {C : Set (ℕ → ℝ)} (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) {p : ℝ × ℝ} (hp : p ∈ smoothParams C)
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (hc : ∀ e, G.latency e ∈ C) : IsSmoothCG G p.1 p.2 := by
  intro A A' _ _
  have hμ := resource_mu_nonneg hne hC hp
  let K : CongestionGame ι E := ⟨G.strategies, fun e _ => G.latency e (load A e + 1)⟩
  have hdev : (∑ i, cost G (Function.update A i (A' i)) i) ≤ sumCost K A' := by
    apply Finset.sum_le_sum
    intro i _
    unfold cost
    rw [Function.update_self]
    apply Finset.sum_le_sum
    intro e he
    exact (hC _ (hc e)).2.1 _ _ (load_pos (i := i) (by simpa only [Function.update_self] using he)) (load_update_le A i (A' i) e)
  rw [sumCost_eq_resource_sum K A'] at hdev
  have hres : (∑ e, G.latency e (load A e + 1) * (load A' e : ℝ)) ≤
      ∑ e, (p.1 * (G.latency e (load A' e) * (load A' e : ℝ)) +
        p.2 * (G.latency e (load A e) * (load A e : ℝ))) := by
    apply Finset.sum_le_sum
    intro e _
    by_cases he : load A' e = 0
    · simpa [he] using mul_nonneg hμ (cost_mass_nonneg (hC _ (hc e)) (load A e))
    · exact hp.2 _ (hc e) _ _ (by omega)
  have hsum : (∑ e, (p.1 * (G.latency e (load A' e) * (load A' e : ℝ)) +
        p.2 * (G.latency e (load A e) * (load A e : ℝ)))) =
      p.1 * sumCost G A' + p.2 * sumCost G A := by
    rw [sumCost_eq_resource_sum G A', sumCost_eq_resource_sum G A]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  exact hdev.trans (hres.trans_eq hsum)

theorem classInf_le_gamma {C : Set (ℕ → ℝ)} (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) :
    (⨅ p ∈ classParams C, ENNReal.ofReal (p.1 / (1 - p.2))) ≤ gamma C := by
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  have hc : p ∈ classParams C := ⟨hp.1, fun _ _ G hG => resource_smooth hne hC hp G hG.1⟩
  exact iInf_le_of_le p (iInf_le_of_le hc le_rfl)

theorem worst_le_classInf {C : Set (ℕ → ℝ)} (hC : ∀ c ∈ C, IsCostFn c) :
    worstPoA C ≤ ⨅ p ∈ classParams C, ENNReal.ofReal (p.1 / (1 - p.2)) := by
  refine le_iInf fun p => le_iInf fun hp => ?_
  refine iSup_le fun k => iSup_le fun m => iSup_le fun G => iSup_le fun hG => ?_
  refine iSup_le fun A => iSup_le fun hA => ?_
  obtain ⟨B, hB, hopt⟩ := exists_opt_profile G hG.2
  have hden : 0 < 1 - p.2 := sub_pos.mpr hp.1
  have hcost : sumCost G A ≤ (p.1 / (1 - p.2)) * sumCost G B := by
    have hn : sumCost G A ≤ ∑ i, cost G (Function.update A i (B i)) i :=
      Finset.sum_le_sum fun i _ => hA.2 i (B i) (hB i)
    have hs := hp.2 k m G hG A B hA.1 hB
    have hx : (1 - p.2) * sumCost G A ≤ p.1 * sumCost G B := by linarith
    have hdiv : sumCost G A ≤ (p.1 * sumCost G B) / (1 - p.2) :=
      (le_div_iff₀ hden).mpr (by nlinarith)
    simpa [div_mul_eq_mul_div] using hdiv
  have hnonneg := sumCost_nonneg hC G hG.1 B
  rw [hopt]
  by_cases hz : sumCost G B = 0
  · have ha0 : sumCost G A = 0 := le_antisymm (by simpa [hz] using hcost)
      (sumCost_nonneg hC G hG.1 A)
    simp [hz, ha0]
  · have hbpos : 0 < sumCost G B := lt_of_le_of_ne hnonneg (Ne.symm hz)
    rw [← ENNReal.ofReal_div_of_pos hbpos]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hbpos).mpr hcost)

end PoATightProof

open scoped BigOperators Classical ENNReal
open CongestionPoA.AsymSum RobustPoA.Tight

namespace PoATightProof

structure LoadConstraint (C : Set (ℕ → ℝ)) where
  cost : ℕ → ℝ
  mem : cost ∈ C
  x : ℕ
  y : ℕ
  hy : 1 ≤ y

namespace LoadConstraint
variable {C : Set (ℕ → ℝ)}
def reference (s : LoadConstraint C) : ℝ := s.cost s.y * (s.y : ℝ)
def current (s : LoadConstraint C) : ℝ := s.cost s.x * (s.x : ℝ)
def excess (s : LoadConstraint C) : ℝ := s.cost (s.x + 1) * (s.y : ℝ) - s.current
end LoadConstraint

open LoadConstraint

theorem one_constraint_bound {C : Set (ℕ → ℝ)} (hC : ∀ c ∈ C, IsCostFn c)
    (hW : worstPoA C ≠ ⊤) (s : LoadConstraint C) (he : 0 ≤ s.excess) :
    s.current ≤ (worstPoA C).toReal * s.reference := by
  have hbal : (∑ _ : Unit, s.cost s.x * (s.x : ℝ)) ≤
      ∑ _ : Unit, s.cost (s.x + 1) * (s.y : ℝ) := by
    simp only [Fintype.sum_unique]
    exact sub_nonneg.mp he
  have hh := finite_witness_bound hC hW (fun _ : Unit => s.cost) (fun _ => s.x)
    (fun _ => s.y) (fun _ => s.mem) (fun _ => s.hy) hbal
  simpa [current, reference] using hh

theorem pair_constraint_bound {C : Set (ℕ → ℝ)} (hC : ∀ c ∈ C, IsCostFn c)
    (hW : worstPoA C ≠ ⊤) (s t : LoadConstraint C) (m n : ℕ)
    (he : 0 ≤ (m : ℝ) * s.excess + (n : ℝ) * t.excess) :
    (m : ℝ) * s.current + (n : ℝ) * t.current ≤
      (worstPoA C).toReal * ((m : ℝ) * s.reference + (n : ℝ) * t.reference) := by
  let c : Fin m ⊕ Fin n → ℕ → ℝ := Sum.elim (fun _ => s.cost) (fun _ => t.cost)
  let x : Fin m ⊕ Fin n → ℕ := Sum.elim (fun _ => s.x) (fun _ => t.x)
  let y : Fin m ⊕ Fin n → ℕ := Sum.elim (fun _ => s.y) (fun _ => t.y)
  have hc : ∀ i, c i ∈ C := by intro i; cases i <;> first | exact s.mem | exact t.mem
  have hy : ∀ i, 1 ≤ y i := by intro i; cases i <;> first | exact s.hy | exact t.hy
  have hbal : (∑ i, c i (x i) * (x i : ℝ)) ≤ ∑ i, c i (x i + 1) * (y i : ℝ) := by
    simp only [Fintype.sum_sum_type, c, x, y, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [excess, current] at he
    nlinarith
  have hh := finite_witness_bound hC hW c x y hc hy hbal
  simpa [c, x, y, current, reference, Fintype.sum_sum_type] using hh

theorem finite_cost_strict {C : Set (ℕ → ℝ)} (hC : ∀ c ∈ C, IsCostFn c)
    (hW : worstPoA C ≠ ⊤) {c : ℕ → ℝ} (hc : c ∈ C) : IsStrictlyPos c := by
  intro z hz
  by_contra hpos
  have hzero : c z = 0 := le_antisymm (le_of_not_gt hpos) ((hC c hc).1 z hz)
  have hex : ∃ n, 1 ≤ n ∧ c n ≠ 0 := (hC c hc).2.2
  let m := Nat.find hex
  have hm : 1 ≤ m ∧ c m ≠ 0 := Nat.find_spec hex
  have hcm : 0 < c m := lt_of_le_of_ne ((hC c hc).1 m hm.1) (Ne.symm hm.2)
  have hzm : z < m := by
    by_contra h
    have hmono := (hC c hc).2.1 m z hm.1 (le_of_not_gt h)
    linarith
  let k := m - 1
  have hk : 1 ≤ k := by omega
  have hkm : k + 1 = m := by omega
  have hck : c k = 0 := by
    by_contra h
    have := Nat.find_min' hex (show 1 ≤ k ∧ c k ≠ 0 from ⟨hk, h⟩)
    change m ≤ k at this
    omega
  let s : LoadConstraint C := ⟨c, hc, k, k, hk⟩
  let t : LoadConstraint C := ⟨c, hc, k + 1, k, hk⟩
  have hmono := (hC c hc).2.1 (k + 1) (k + 1 + 1) (by omega) (by omega)
  have hcp : 0 < c (k + 1) := by simpa [hkm] using hcm
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : 0 ≤ (1 : ℝ) * s.excess + (1 : ℝ) * t.excess := by
    dsimp [s, t, excess, current]
    rw [hck]
    simp only [zero_mul, sub_zero, Nat.cast_add, Nat.cast_one, one_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') hcp.le,
      mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hmono)]
  have hh := pair_constraint_bound hC hW s t 1 1 (by simpa only [Nat.cast_one] using he)
  dsimp [s, t, current, reference] at hh
  rw [hck] at hh
  simp only [Nat.cast_one, one_mul, zero_mul, zero_add, add_zero, mul_zero] at hh
  have hcp' : 0 < c (k + 1) * ((k + 1 : ℕ) : ℝ) := mul_pos hcp (by positivity)
  linarith

theorem balanced_constraint_bound {C : Set (ℕ → ℝ)} (hC : ∀ c ∈ C, IsCostFn c)
    (hW : worstPoA C ≠ ⊤) (s t : LoadConstraint C)
    (hs : s.excess < 0) (ht : 0 < t.excess) :
    t.excess * s.current - s.excess * t.current ≤
      (worstPoA C).toReal * (t.excess * s.reference - s.excess * t.reference) := by
  have hh := balanced_of_nat s.excess t.excess
    (s.current - (worstPoA C).toReal * s.reference)
    (t.current - (worstPoA C).toReal * t.reference) hs ht (fun m n he => by
      have := pair_constraint_bound hC hW s t m n he
      nlinarith)
  nlinarith

theorem resource_pair_of_gt {C : Set (ℕ → ℝ)} (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) (hW : worstPoA C ≠ ⊤)
    (q : ℝ) (hq : (worstPoA C).toReal < q) :
    ∃ p ∈ smoothParams C, p.1 / (1 - p.2) = q := by
  have hqpos : 0 < q := (ENNReal.toReal_nonneg).trans_lt hq
  have hA (s : LoadConstraint C) : 0 < s.reference :=
    mul_pos (finite_cost_strict hC hW s.mem s.y s.hy) (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one s.hy))
  have hsingle (s : LoadConstraint C) (he : 0 ≤ s.excess) : s.current ≤ q * s.reference :=
    (one_constraint_bound hC hW s he).trans (mul_le_mul_of_nonneg_right hq.le (hA s).le)
  have hpair (s t : LoadConstraint C) (hs : s.excess < 0) (ht : 0 < t.excess) :
      (s.current - q * s.reference) / (-s.excess) ≤
        (q * t.reference - t.current) / t.excess := by
    apply (div_le_div_iff₀ (neg_pos.mpr hs) ht).mpr
    have hh := balanced_constraint_bound hC hW s t hs ht
    have hpos : 0 < t.excess * s.reference - s.excess * t.reference := by
      nlinarith [mul_pos ht (hA s), mul_pos (neg_pos.mpr hs) (hA t)]
    have hweak := mul_le_mul_of_nonneg_right hq.le hpos.le
    nlinarith
  obtain ⟨c, hc⟩ := hne
  let u : LoadConstraint C := ⟨c, hc, 0, 1, by omega⟩
  have hu : 0 < u.excess := by
    simpa [u, excess, current] using finite_cost_strict hC hW hc 1 (by omega)
  obtain ⟨n, hn⟩ := exists_nat_gt (max q 1)
  have hnq : q < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hn1 : 1 ≤ n := by exact_mod_cast ((le_max_right _ _).trans_lt hn).le
  let v : LoadConstraint C := ⟨c, hc, n, 1, by omega⟩
  have hc1 := finite_cost_strict hC hW hc 1 (by omega)
  have hcn := (hC c hc).2.1 1 n (by omega) hn1
  have hv : q * v.reference < v.current := by
    dsimp [v, reference, current]
    simp only [Nat.cast_one, mul_one]
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hcn),
      mul_pos (sub_pos.mpr hnq) hc1]
  have hve : v.excess < 0 := by
    by_contra h
    exact (not_lt_of_ge (hsingle v (le_of_not_gt h))) hv
  obtain ⟨t, ht, hall⟩ := interval_common_point reference current excess q
    (fun s hs => hsingle s hs.ge) hpair ⟨u, hu⟩
    ⟨v, hve, div_pos (sub_pos.mpr hv) (neg_pos.mpr hve)⟩
  refine ⟨(q / t, 1 - 1 / t), ⟨?_, ?_⟩, ?_⟩
  · have := one_div_pos.mpr ht
    linarith
  · intro d hd x y hy
    have hh := hall (⟨d, hd, x, y, hy⟩ : LoadConstraint C)
    dsimp [current, excess, reference] at hh
    apply (mul_le_mul_iff_right₀ ht).mp
    have heq : t * ((q / t) * (d y * (y : ℝ)) +
        (1 - 1 / t) * (d x * (x : ℝ))) =
        q * (d y * (y : ℝ)) + (t - 1) * (d x * (x : ℝ)) := by
      field_simp
    rw [heq]
    nlinarith
  · dsimp
    field_simp
    ring

theorem gamma_le_worst {C : Set (ℕ → ℝ)} (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) : gamma C ≤ worstPoA C := by
  by_cases hW : worstPoA C = ⊤
  · simp [hW]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0 : ℝ) < ε := hε
  obtain ⟨p, hp, hratio⟩ := resource_pair_of_gt hne hC hW
    ((worstPoA C).toReal + ε) (by linarith)
  have hh : gamma C ≤ ENNReal.ofReal ((worstPoA C).toReal + ε) := by
    exact iInf_le_of_le p (iInf_le_of_le hp (by rw [hratio]))
  simpa [ENNReal.ofReal_add ENNReal.toReal_nonneg (NNReal.coe_nonneg ε),
    ENNReal.ofReal_toReal hW] using hh

end PoATightProof

namespace RobustPoA.Tight

open scoped ENNReal

/-- Theorem 5.8, p. 30, stated as (34), p. 23: for every nonempty class of
nonnegative, nondecreasing, nonzero cost functions, the congestion-game class is tight. -/
theorem theorem_5_8 (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) :
    worstPoA C =
      ⨅ p ∈ classParams C, ENNReal.ofReal (p.1 / (1 - p.2)) := by
  apply le_antisymm
  · exact PoATightProof.worst_le_classInf hC
  · exact (PoATightProof.classInf_le_gamma hne hC).trans
      (PoATightProof.gamma_le_worst hne hC)

end RobustPoA.Tight

open RobustPoA.Tight

theorem solution (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) :
    worstPoA C =
      ⨅ p ∈ classParams C, ENNReal.ofReal (p.1 / (1 - p.2)) := by
  exact RobustPoA.Tight.theorem_5_8 C hne hC
