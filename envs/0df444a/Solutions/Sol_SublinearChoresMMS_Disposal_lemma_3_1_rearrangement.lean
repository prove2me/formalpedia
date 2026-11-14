-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.lemma_3_1_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:26:27.376503+00:00
-- url     : https://prove2.me/submissions/9261ad68-ff4d-4cc3-8cc5-572d7e6cd5d2

import Definitions.Def_SublinearChoresMMS_Disposal_Packing
import Mathlib
section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
/-!
# Appendix A.1.3 (rearranging a packing into few segments), Blueprint

An abstract core: items `Fin N` with strictly decreasing positive sizes `s`, bins `Fin b` with
capacities `T`, an assignment `P : Fin N → Option (Fin b)` (`none` = excluded).  The core turns a
valid assignment into one with at most `5d` more exclusions and `O(d b²)` label changes, for any
`d ≥ 1` with `b ≤ d²`.  The route is the paper's: exclude the `2d` costliest items (slack), split
the rest into `d` cost ranges, keep the `b(b-1)` cheapest of each range fixed, take a basic optimal
solution of the LP minimizing `∑ v·a²·z`, round it along monotone cycles (at most `b-1` updates),
repair gaining bins by swaps with fixed items, repack the slack bins.
-/
abbrev Asg (N b : ℕ) := Fin N → Option (Fin b)

def load (s : Fin N → ℝ) (P : Asg N b) (v : Fin b) : ℝ :=
  ∑ r, if P r = some v then s r else 0

def excl (P : Asg N b) : ℕ := (univ.filter fun r => P r = none).card

def changes (P : Asg N b) : ℕ :=
  (univ.filter fun r : Fin N => ∃ h : r.val + 1 < N, P r ≠ P ⟨r.val + 1, h⟩).card

/-- Cost range index (0-based) of a size `x ∈ (0, κ]`: `x ∈ (kκ/d, (k+1)κ/d]`. -/
def rk (κ : ℝ) (d : ℕ) (x : ℝ) : ℕ := ⌈x * d / κ⌉₊ - 1

/-- Fixed items: the `b(b-1)` cheapest non-excluded items of each range (larger index = cheaper). -/
def IsFixed (s : Fin N → ℝ) (κ : ℝ) (d : ℕ) (P1 : Asg N b) (r : Fin N) : Prop :=
  P1 r ≠ none ∧
    (univ.filter fun r' => r < r' ∧ P1 r' ≠ none ∧ rk κ d (s r') = rk κ d (s r)).card < b * (b - 1)

/-- Movable items: non-excluded and not fixed. -/
def movable (s : Fin N → ℝ) (κ : ℝ) (d : ℕ) (P1 : Asg N b) : Finset (Fin N) :=
  univ.filter fun r => P1 r ≠ none ∧ ¬ IsFixed s κ d P1 r

end SublinearChoresMMS.Dev.Rearr
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartCore
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}

/-- Exclude the items of `E`. -/
def exclOn (P : Asg N b) (E : Finset (Fin N)) : Asg N b := fun r => if r ∈ E then none else P r

lemma load_exclOn_le (s : Fin N → ℝ) (hpos : ∀ r, 0 < s r) (P : Asg N b) (E : Finset (Fin N))
    (v : Fin b) : load s (exclOn P E) v ≤ load s P v := by
  unfold load exclOn
  apply sum_le_sum
  intro r _
  by_cases hr : r ∈ E
  · simp only [hr, if_true]
    split_ifs <;> simp_all [(hpos r).le]
  · simp [hr]

lemma excl_exclOn_le (P : Asg N b) (E : Finset (Fin N)) :
    excl (exclOn P E) ≤ excl P + E.card := by
  unfold excl
  calc (univ.filter fun r => exclOn P E r = none).card
      ≤ ((univ.filter fun r => P r = none) ∪ E).card := by
        apply card_le_card
        intro r hr
        simp only [exclOn] at hr
        simp only [mem_union, mem_filter, mem_univ, true_and]
        by_cases h : r ∈ E
        · exact Or.inr h
        · simp [h] at hr; exact Or.inl hr
    _ ≤ _ := card_union_le _ _

lemma sum_load_diff (s : Fin N → ℝ) (P : Asg N b) (E : Finset (Fin N))
    (hE : ∀ r ∈ E, P r ≠ none) :
    ∑ v ∈ E.biUnion (fun r => (P r).toFinset), (load s P v - load s (exclOn P E) v) =
      ∑ r ∈ E, s r := by
  have h1 : ∀ v, load s P v - load s (exclOn P E) v =
      ∑ r ∈ E, if P r = some v then s r else 0 := by
    intro v
    unfold load exclOn
    rw [← sum_sub_distrib, ← sum_filter_add_sum_filter_not univ (fun r => r ∈ E)]
    have h2 : ∑ x ∈ univ.filter (fun r => r ∉ E), ((if P x = some v then s x else 0) -
        if (if x ∈ E then none else P x) = some v then s x else 0) = 0 := by
      apply sum_eq_zero
      intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      simp [hr]
    rw [h2, add_zero, filter_mem_eq_inter, univ_inter]
    apply sum_congr rfl
    intro r hr
    simp [hr]
  simp_rw [h1]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  obtain ⟨v0, hv0⟩ := Option.ne_none_iff_exists'.mp (hE r hr)
  rw [hv0]
  simp only [Option.some.injEq]
  rw [sum_ite_eq]
  have : v0 ∈ E.biUnion (fun r => (P r).toFinset) := by
    rw [mem_biUnion]; exact ⟨r, hr, by simp [hv0]⟩
  simp [this]

lemma card_biUnion_toFinset_le (P : Asg N b) (E : Finset (Fin N)) :
    (E.biUnion (fun r => (P r).toFinset)).card ≤ E.card := by
  calc _ ≤ ∑ r ∈ E, ((P r).toFinset).card := card_biUnion_le
    _ ≤ ∑ r ∈ E, 1 := by
        apply sum_le_sum; intro r _
        cases P r <;> simp
    _ = E.card := by simp

theorem step1 (N b d : ℕ) (s : Fin N → ℝ) (hs : StrictAnti s) (hpos : ∀ r, 0 < s r)
    (T : Fin b → ℝ) (P : Asg N b) (hP : ∀ v, load s P v ≤ T v) :
    ∃ (P1 : Asg N b) (κ : ℝ) (V : Finset (Fin b)), 0 ≤ κ ∧ V.card ≤ 2 * d ∧
      (∀ r, P1 r = none ∨ P1 r = P r) ∧ excl P1 ≤ excl P + 2 * d ∧
      (∀ r, P1 r ≠ none → s r ≤ κ) ∧
      2 * d * κ ≤ ∑ v ∈ V, (T v - load s P1 v) ∧ (∀ v, load s P1 v ≤ T v) := by
  set K : Finset (Fin N) := univ.filter fun r => P r ≠ none with hK
  by_cases hsmall : K.card ≤ 2 * d
  · -- exclude everything
    refine ⟨exclOn P univ, 0, ∅, le_rfl, by simp, ?_, ?_, ?_, by simp, ?_⟩
    · intro r; left; simp [exclOn]
    · unfold excl
      have hsplit := card_filter_add_card_filter_not
        (s := (univ : Finset (Fin N))) (fun r => P r = none)
      have : (univ.filter fun r => exclOn P univ r = none) = univ := by
        ext r; simp [exclOn]
      rw [this]
      have hK' : (univ.filter fun r => ¬ P r = none) = K := by rw [hK]
      rw [hK'] at hsplit
      omega
    · intro r hr; simp [exclOn] at hr
    · intro v; exact (load_exclOn_le s hpos P univ v).trans (hP v)
  · push Not at hsmall
    set ρ : Fin N → ℕ := fun r => (K.filter (· < r)).card with hρ
    have hρmono : ∀ r r', r ≤ r' → ρ r ≤ ρ r' := by
      intro r r' h
      apply card_le_card
      intro x hx
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩
    have hρstrict : ∀ r ∈ K, ∀ r', r < r' → ρ r < ρ r' := by
      intro r hr r' h
      apply card_lt_card
      rw [ssubset_iff_of_subset]
      · exact ⟨r, by simp [hr, h], by simp⟩
      · intro x hx
        simp only [mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.trans h⟩
    set E : Finset (Fin N) := K.filter fun r => ρ r < 2 * d with hE
    have hEK : E ⊆ K := filter_subset _ _
    have hEcard : E.card ≤ 2 * d := by
      calc E.card ≤ (range (2 * d)).card := by
            apply card_le_card_of_injOn ρ
            · intro r hr
              simp only [hE, coe_filter, Set.mem_ofPred_eq] at hr
              simp [hr.2]
            · intro r hr r' hr' heq
              simp only [hE, coe_filter, Set.mem_ofPred_eq] at hr hr'
              rcases lt_trichotomy r r' with h | h | h
              · exact absurd heq (hρstrict r hr.1 r' h).ne
              · exact h
              · exact absurd heq (hρstrict r' hr'.1 r h).ne'
        _ = 2 * d := card_range _
    have hne : (K \ E).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset hEK]; omega
    set rs := (K \ E).min' hne with hrs
    have hrsKE : rs ∈ K \ E := min'_mem _ _
    have hrsK : rs ∈ K := (mem_sdiff.mp hrsKE).1
    have hrsE : rs ∉ E := (mem_sdiff.mp hrsKE).2
    have hrsρ : 2 * d ≤ ρ rs := by
      by_contra h; push Not at h
      exact hrsE (by simp [hE, hrsK, h])
    have hlt : ∀ r ∈ E, r < rs := by
      intro r hr
      by_contra h; push Not at h
      have := hρmono _ _ h
      have hr2 : ρ r < 2 * d := (mem_filter.mp hr).2
      omega
    have hEcard2 : 2 * d ≤ E.card := by
      refine hrsρ.trans (card_le_card ?_)
      intro x hx
      simp only [mem_filter] at hx
      by_contra hxE
      have : rs ≤ x := min'_le _ _ (by simp [hx.1, hxE])
      exact absurd hx.2 (not_lt.mpr this)
    refine ⟨exclOn P E, s rs, E.biUnion (fun r => (P r).toFinset), (hpos rs).le,
      (card_biUnion_toFinset_le P E).trans hEcard, ?_, ?_, ?_, ?_, ?_⟩
    · intro r; unfold exclOn; split_ifs <;> simp
    · exact (excl_exclOn_le P E).trans (by omega)
    · intro r hr
      unfold exclOn at hr
      split_ifs at hr with h
      · exact absurd rfl hr
      · have hrK : r ∈ K := by simp [hK, hr]
        exact hs.antitone (min'_le _ _ (by simp [hrK, h]))
    · have hEne : ∀ r ∈ E, P r ≠ none := fun r hr => (mem_filter.mp (hEK hr)).2
      calc 2 * (d : ℝ) * s rs ≤ (E.card : ℝ) * s rs := by
            apply mul_le_mul_of_nonneg_right _ (hpos rs).le
            exact_mod_cast hEcard2
        _ = ∑ r ∈ E, s rs := by simp
        _ ≤ ∑ r ∈ E, s r := sum_le_sum fun r hr => (hs (hlt r hr)).le
        _ = ∑ v ∈ E.biUnion (fun r => (P r).toFinset), (load s P v - load s (exclOn P E) v) :=
            (sum_load_diff s P E hEne).symm
        _ ≤ _ := sum_le_sum fun v _ => by linarith [hP v]
    · intro v; exact (load_exclOn_le s hpos P E v).trans (hP v)

end SublinearChoresMMS.Dev.Rearr.PartCore
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
/-! ## Stubs -/
alias step1 := SublinearChoresMMS.Dev.Rearr.PartCore.step1

end SublinearChoresMMS.Dev.Rearr
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartLP
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
/-- The feasible set of the structured LP. -/
def Feas (s : Fin N → ℝ) (Mv : Finset (Fin N)) (rk : Fin N → ℕ) (y0 : Fin N → Fin b)
    (z : Fin N → Fin b → ℝ) : Prop :=
  (∀ r v, 0 ≤ z r v) ∧ (∀ r ∉ Mv, ∀ v, z r v = 0) ∧ (∀ r ∈ Mv, ∑ v, z r v = 1) ∧
    (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), z r v =
      ((Mv.filter fun r => rk r = k ∧ y0 r = v).card : ℝ)) ∧
    (∀ v, ∑ r ∈ Mv, s r * z r v = ∑ r ∈ Mv.filter (fun r => y0 r = v), s r)

/-- Directions preserving all equality constraints. -/
def Dir (s : Fin N → ℝ) (Mv : Finset (Fin N)) (rk : Fin N → ℕ) (δ : Fin N → Fin b → ℝ) :
    Prop :=
  (∀ r ∉ Mv, ∀ v, δ r v = 0) ∧ (∀ r, ∑ v, δ r v = 0) ∧
    (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0) ∧
    (∀ v, ∑ r ∈ Mv, s r * δ r v = 0)

/-- The objective `∑ v·a²·z`. -/
def Phi (s : Fin N → ℝ) (z : Fin N → Fin b → ℝ) : ℝ :=
  ∑ r, ∑ v : Fin b, ((v : ℕ) : ℝ) * s r ^ 2 * z r v

/-- The fractional entries. -/
def frac (z : Fin N → Fin b → ℝ) : Finset (Fin N × Fin b) :=
  univ.filter fun p => 0 < z p.1 p.2 ∧ z p.1 p.2 < 1

end SublinearChoresMMS.Dev.Rearr.PartLP
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartLP
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
variable {s : Fin N → ℝ} {Mv : Finset (Fin N)} {rk : Fin N → ℕ} {y0 : Fin N → Fin b}
lemma feas_add {z δ : Fin N → Fin b → ℝ} (hz : Feas s Mv rk y0 z) (hδ : Dir s Mv rk δ) (t : ℝ)
    (hnn : ∀ r v, 0 ≤ z r v + t * δ r v) :
    Feas s Mv rk y0 (fun r v => z r v + t * δ r v) := by
  obtain ⟨_, h1, h2, h3, h4⟩ := hz
  obtain ⟨d1, d2, d3, d4⟩ := hδ
  refine ⟨hnn, fun r hr v => by simp [h1 r hr v, d1 r hr v], fun r hr => ?_,
    fun v k => ?_, fun v => ?_⟩
  · rw [sum_add_distrib, ← mul_sum, d2 r, h2 r hr]; ring
  · rw [sum_add_distrib, ← mul_sum, d3 v k, h3 v k]; ring
  · simp only [mul_add, sum_add_distrib]
    rw [h4 v]
    have : ∑ r ∈ Mv, s r * (t * δ r v) = t * ∑ r ∈ Mv, s r * δ r v := by
      rw [mul_sum]; exact sum_congr rfl fun r _ => by ring
    rw [this, d4 v]; ring

lemma phi_add (z δ : Fin N → Fin b → ℝ) (t : ℝ) :
    Phi s (fun r v => z r v + t * δ r v) = Phi s z + t * Phi s δ := by
  simp only [Phi, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun r _ => sum_congr rfl fun v _ => by ring

lemma Feas.le_one {z : Fin N → Fin b → ℝ} (h : Feas s Mv rk y0 z) (r : Fin N) (v : Fin b) :
    z r v ≤ 1 := by
  by_cases hr : r ∈ Mv
  · rw [← h.2.2.1 r hr]; exact single_le_sum (fun w _ => h.1 r w) (mem_univ v)
  · rw [h.2.1 r hr v]; norm_num

lemma feas_ind : Feas s Mv rk y0 (fun r v => if r ∈ Mv ∧ y0 r = v then 1 else 0) := by
  refine ⟨fun r v => by dsimp only; split_ifs <;> norm_num, fun r hr v => by simp [hr],
    fun r hr => ?_, fun v k => ?_, fun v => ?_⟩
  · simp [hr]
  · rw [sum_boole]
    congr 2
    ext r
    simp only [mem_filter]
    tauto
  · rw [sum_filter]
    refine sum_congr rfl fun r hr => ?_
    simp [hr]

lemma isClosed_feas : IsClosed {z | Feas s Mv rk y0 z} := by
  simp only [Feas, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · exact isClosed_iInter fun r => isClosed_iInter fun v =>
      isClosed_le continuous_const (by fun_prop)
  · exact isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun v =>
      isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun r => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun v => isClosed_iInter fun k =>
      isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun v => isClosed_eq (by fun_prop) continuous_const

lemma isCompact_feas : IsCompact {z | Feas s Mv rk y0 z} := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_feas
    ((Metric.isBounded_Icc (0 : Fin N → Fin b → ℝ) 1).subset ?_)
  intro z hz
  exact ⟨fun r v => hz.1 r v, fun r v => Feas.le_one hz r v⟩

lemma continuous_phi : Continuous (Phi (b := b) s) := by
  unfold Phi; fun_prop

/-- The order property at a minimizer (three-point perturbation). -/
lemma order_of_min {zm : Fin N → Fin b → ℝ} (hzm : Feas s Mv rk y0 zm)
    (hmin : ∀ z, Feas s Mv rk y0 z → Phi s zm ≤ Phi s z)
    (u v : Fin b) (r1 r2 r3 : Fin N) (h1 : r1 ∈ Mv) (h2 : r2 ∈ Mv) (h3 : r3 ∈ Mv)
    (e12 : rk r1 = rk r2) (e23 : rk r2 = rk r3) (l12 : s r1 < s r2) (l23 : s r2 < s r3)
    (p1 : 0 < zm r1 u) (p2 : 0 < zm r2 v) (p3 : 0 < zm r3 u) (huv : u ≠ v) : u < v := by
  rcases lt_or_gt_of_ne huv with h | h
  · exact h
  exfalso
  have n12 : r1 ≠ r2 := fun h => by rw [h] at l12; exact lt_irrefl _ l12
  have n23 : r2 ≠ r3 := fun h => by rw [h] at l23; exact lt_irrefl _ l23
  have n13 : r1 ≠ r3 := fun h => by rw [h] at l12; exact lt_irrefl _ (l12.trans l23)
  let c : Fin N → ℝ := fun r => (if r = r1 then s r3 - s r2 else 0) +
    (if r = r2 then -(s r3 - s r1) else 0) + (if r = r3 then s r2 - s r1 else 0)
  let e : Fin b → ℝ := fun w => (if w = v then 1 else 0) - (if w = u then 1 else 0)
  let δ : Fin N → Fin b → ℝ := fun r w => c r * e w
  have hdir : Dir s Mv rk δ := by
    refine ⟨fun r hr w => ?_, fun r => ?_, fun w k => ?_, fun w => ?_⟩
    · have : c r = 0 := by
        simp only [c]
        rw [if_neg, if_neg, if_neg] <;> [ring; (rintro rfl; exact hr h3);
          (rintro rfl; exact hr h2); (rintro rfl; exact hr h1)]
      simp [δ, this]
    · simp only [δ, ← mul_sum, e, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, sub_self,
        mul_zero]
    · simp only [δ, ← sum_mul, c, sum_add_distrib, sum_ite_eq', mem_filter, h1, h2, h3,
        true_and]
      rw [← e23, ← e12]
      split_ifs <;> ring
    · have : ∑ r ∈ Mv, s r * δ r w = e w * ∑ r ∈ Mv, s r * c r := by
        rw [mul_sum]; exact sum_congr rfl fun r _ => by simp only [δ]; ring
      rw [this]
      simp only [c, mul_add, mul_ite, mul_zero, sum_add_distrib, sum_ite_eq', h1, h2, h3,
        if_true]
      ring
  have hphi : Phi s δ = (∑ r, s r ^ 2 * c r) * ∑ w : Fin b, ((w : ℕ) : ℝ) * e w := by
    rw [sum_mul]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun w _ => by simp only [δ]; ring
  have he : ∑ w : Fin b, ((w : ℕ) : ℝ) * e w = ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ) := by
    simp only [e, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ,
      if_true]
  have hc : ∑ r, s r ^ 2 * c r = (s r2 - s r1) * (s r3 - s r2) * (s r3 - s r1) := by
    simp only [c, mul_add, mul_ite, mul_zero, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    ring
  have hvu : ((v : ℕ) : ℝ) < ((u : ℕ) : ℝ) := by exact_mod_cast h
  have hneg : Phi s δ < 0 := by
    rw [hphi, he, hc]
    have : 0 < (s r2 - s r1) * (s r3 - s r2) * (s r3 - s r1) := by
      apply mul_pos (mul_pos _ _) <;> linarith
    nlinarith
  set m := min (zm r1 u) (min (zm r2 v) (zm r3 u)) with hm
  have hmpos : 0 < m := lt_min p1 (lt_min p2 p3)
  have hd : 0 < s r3 - s r1 := by linarith
  set t := m / (s r3 - s r1) with ht
  have htpos : 0 < t := div_pos hmpos hd
  have htd : t * (s r3 - s r1) = m := by rw [ht]; field_simp
  have m1 : m ≤ zm r1 u := min_le_left _ _
  have m2 : m ≤ zm r2 v := (min_le_right _ _).trans (min_le_left _ _)
  have m3 : m ≤ zm r3 u := (min_le_right _ _).trans (min_le_right _ _)
  have hnn : ∀ r w, 0 ≤ zm r w + t * δ r w := by
    intro r w
    have hz := hzm.1 r w
    have hvu' : v ≠ u := huv.symm
    have a1 : t * (s r3 - s r2) ≤ t * (s r3 - s r1) :=
      mul_le_mul_of_nonneg_left (by linarith) htpos.le
    have a2 : t * (s r2 - s r1) ≤ t * (s r3 - s r1) :=
      mul_le_mul_of_nonneg_left (by linarith) htpos.le
    have a3 : 0 ≤ t * (s r3 - s r2) := mul_nonneg htpos.le (by linarith)
    have a4 : 0 ≤ t * (s r2 - s r1) := mul_nonneg htpos.le (by linarith)
    simp only [δ, c, e]
    by_cases hr1 : r = r1
    · subst hr1
      by_cases hw : w = u
      · subst hw; simp [n12, n13, hvu', huv, hvu']; nlinarith
      · simp [n12, n13, hw]; split_ifs <;> nlinarith
    by_cases hr2 : r = r2
    · subst hr2
      by_cases hw : w = v
      · subst hw; simp [hr1, n23, huv, huv, hvu']; nlinarith
      · simp [hr1, n23, hw]; split_ifs <;> nlinarith
    by_cases hr3 : r = r3
    · subst hr3
      by_cases hw : w = u
      · subst hw; simp [hr1, hr2, hvu', huv, hvu']; nlinarith
      · simp [hr1, hr2, hw]; split_ifs <;> nlinarith
    simp [hr1, hr2, hr3, hz]
  have hfe := feas_add hzm hdir t hnn
  have := hmin _ hfe
  rw [phi_add] at this
  nlinarith

/-- One reduction step: a nonzero direction on fractional entries lowers the fractional count. -/
lemma reduce {z δ : Fin N → Fin b → ℝ} (hz : Feas s Mv rk y0 z)
    (hδ1 : ∀ r v, δ r v ≠ 0 → 0 < z r v ∧ z r v < 1) (hδ2 : ∀ r, ∑ v, δ r v = 0)
    (hδ3 : ∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0)
    (hδ4 : ∀ v, ∑ r, s r * δ r v = 0) (hne : δ ≠ 0) :
    ∃ z', Feas s Mv rk y0 z' ∧ (∀ r v, 0 < z' r v → 0 < z r v) ∧
      (frac z').card < (frac z).card := by
  have d1 : ∀ r ∉ Mv, ∀ v, δ r v = 0 := by
    intro r hr v
    by_contra h
    have := (hδ1 r v h).1
    rw [hz.2.1 r hr v] at this
    exact lt_irrefl _ this
  have hdir : Dir s Mv rk δ := by
    refine ⟨d1, hδ2, hδ3, fun v => ?_⟩
    rw [← hδ4 v]
    exact sum_subset (subset_univ _) fun r _ hr => by rw [d1 r hr v, mul_zero]
  obtain ⟨r, v, hrv⟩ : ∃ r v, δ r v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext fun r => funext fun v => h r v)
  let P := univ.filter fun p : Fin N × Fin b => δ p.1 p.2 ≠ 0
  let g : Fin N × Fin b → ℝ := fun p =>
    if 0 < δ p.1 p.2 then (1 - z p.1 p.2) / δ p.1 p.2 else z p.1 p.2 / (-δ p.1 p.2)
  have hPne : P.Nonempty := ⟨(r, v), by simp [P, hrv]⟩
  obtain ⟨p0, hp0, hmin⟩ := P.exists_min_image g hPne
  set t := g p0 with ht
  have hp0' : δ p0.1 p0.2 ≠ 0 := by simpa [P] using hp0
  have htnn : 0 ≤ t := by
    obtain ⟨a1, a2⟩ := hδ1 _ _ hp0'
    simp only [ht, g]
    split_ifs with hpos
    · exact div_nonneg (by linarith) hpos.le
    · exact div_nonneg a1.le (by push Not at hpos; linarith [lt_of_le_of_ne hpos hp0'])
  have hbd : ∀ r v, 0 ≤ z r v + t * δ r v ∧ z r v + t * δ r v ≤ 1 := by
    intro r v
    have z0 := hz.1 r v
    have z1 := hz.le_one r v
    by_cases h0 : δ r v = 0
    · simp [h0, z0, z1]
    have hle : t ≤ g (r, v) := hmin (r, v) (by simp [P, h0])
    simp only [g] at hle
    split_ifs at hle with hpos
    · rw [le_div_iff₀ hpos] at hle
      constructor <;> nlinarith
    · have hneg : δ r v < 0 := lt_of_le_of_ne (not_lt.mp hpos) h0
      rw [le_div_iff₀ (by linarith)] at hle
      constructor <;> nlinarith
  refine ⟨fun r v => z r v + t * δ r v, feas_add hz hdir t fun r v => (hbd r v).1,
    fun r v hp => ?_, ?_⟩
  · by_cases h0 : δ r v = 0
    · simpa [h0] using hp
    · exact (hδ1 r v h0).1
  · apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨p0, ?_, ?_⟩
      · simpa [frac] using hδ1 _ _ hp0'
      · simp only [frac, mem_filter, mem_univ, true_and, not_and, not_lt]
        intro hp
        by_cases hpos : 0 < δ p0.1 p0.2
        · have e : t = (1 - z p0.1 p0.2) / δ p0.1 p0.2 := by simp only [ht, g, if_pos hpos]
          rw [e, div_mul_cancel₀ _ hp0']; linarith
        · exfalso
          have e : t = z p0.1 p0.2 / -δ p0.1 p0.2 := by simp only [ht, g, if_neg hpos]
          rw [e] at hp
          have : z p0.1 p0.2 + z p0.1 p0.2 / -δ p0.1 p0.2 * δ p0.1 p0.2 = 0 := by
            have : -δ p0.1 p0.2 ≠ 0 := neg_ne_zero.mpr hp0'
            field_simp
            ring
          linarith
    · intro p hp
      simp only [frac, mem_filter, mem_univ, true_and] at hp ⊢
      by_cases h0 : δ p.1 p.2 = 0
      · simpa [h0] using hp
      · exact hδ1 _ _ h0

theorem lp_basic (s : Fin N → ℝ) (Mv : Finset (Fin N)) (rk : Fin N → ℕ) (y0 : Fin N → Fin b) :
    ∃ z : Fin N → Fin b → ℝ, (∀ r v, 0 ≤ z r v) ∧ (∀ r ∉ Mv, ∀ v, z r v = 0) ∧
      (∀ r ∈ Mv, ∑ v, z r v = 1) ∧
      (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), z r v =
        ((Mv.filter fun r => rk r = k ∧ y0 r = v).card : ℝ)) ∧
      (∀ v, ∑ r ∈ Mv, s r * z r v = ∑ r ∈ Mv.filter (fun r => y0 r = v), s r) ∧
      (∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
        s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v) ∧
      (∀ δ : Fin N → Fin b → ℝ, (∀ r v, δ r v ≠ 0 → 0 < z r v ∧ z r v < 1) →
        (∀ r, ∑ v, δ r v = 0) →
        (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0) →
        (∀ v, ∑ r, s r * δ r v = 0) → δ = 0) := by
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_feas (s := s) (Mv := Mv) (rk := rk) (y0 := y0)).exists_isMinOn
    ⟨_, feas_ind⟩ (continuous_phi (s := s)).continuousOn
  have hzm' : Feas s Mv rk y0 zm := hzm
  have hmin' : ∀ z, Feas s Mv rk y0 z → Phi s zm ≤ Phi s z := fun z hz => hmin hz
  have key : ∀ n, ∀ z, Feas s Mv rk y0 z → (∀ r v, 0 < z r v → 0 < zm r v) →
      (frac z).card = n → ∃ z', Feas s Mv rk y0 z' ∧ (∀ r v, 0 < z' r v → 0 < zm r v) ∧
      (∀ δ : Fin N → Fin b → ℝ, (∀ r v, δ r v ≠ 0 → 0 < z' r v ∧ z' r v < 1) →
        (∀ r, ∑ v, δ r v = 0) →
        (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0) →
        (∀ v, ∑ r, s r * δ r v = 0) → δ = 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz hs hn
      by_cases hb : ∀ δ : Fin N → Fin b → ℝ, (∀ r v, δ r v ≠ 0 → 0 < z r v ∧ z r v < 1) →
          (∀ r, ∑ v, δ r v = 0) →
          (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0) →
          (∀ v, ∑ r, s r * δ r v = 0) → δ = 0
      · exact ⟨z, hz, hs, hb⟩
      · push Not at hb
        obtain ⟨δ, d1, d2, d3, d4, hne⟩ := hb
        obtain ⟨z', hz', hs', hlt⟩ := reduce hz d1 d2 d3 d4 hne
        exact ih _ (hn ▸ hlt) z' hz' (fun r v h => hs r v (hs' r v h)) rfl
  obtain ⟨z, hz, hsupp, hb⟩ := key _ zm hzm' (fun _ _ h => h) rfl
  obtain ⟨f0, f1, f2, f3, f4⟩ := hz
  exact ⟨z, f0, f1, f2, f3, f4,
    fun u v r1 h1 r2 h2 r3 h3 e12 e23 l12 l23 p1 p2 p3 huv =>
      order_of_min hzm' hmin' u v r1 r2 r3 h1 h2 h3 e12 e23 l12 l23
        (hsupp _ _ p1) (hsupp _ _ p2) (hsupp _ _ p3) huv, hb⟩

end SublinearChoresMMS.Dev.Rearr.PartLP
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
alias lp_basic := SublinearChoresMMS.Dev.Rearr.PartLP.lp_basic

end SublinearChoresMMS.Dev.Rearr
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartCyc
open SublinearChoresMMS.Dev.Rearr
/-! ## Combinatorics of cyclic sequences -/
/-- The value `c` lies strictly inside the chord `{a, b}` and `d` strictly outside it. -/
def Sep (a b c d : ℝ) : Prop := min a b < c ∧ c < max a b ∧ (d < min a b ∨ max a b < d)

/-- A cycle of length `L`, indexed periodically by `ℤ`: bin `F i` joins items `C i`, `C (i+1)`;
items and bins are distinct modulo `L`. -/
def Cyc {α β : Type*} (E : α → β → Prop) (L : ℕ) (C : ℤ → α) (F : ℤ → β) : Prop :=
  2 ≤ L ∧ (∀ i, E (C i) (F i)) ∧ (∀ i, E (C (i + 1)) (F i)) ∧
    (∀ i j, C i = C j ↔ i ≡ j [ZMOD L]) ∧ (∀ i j, F i = F j ↔ i ≡ j [ZMOD L])

lemma exists_flip (p : ℕ → Prop) (n : ℕ) (h0 : p 0) (hn : ¬ p n) :
    ∃ t < n, p t ∧ ¬ p (t + 1) := by
  induction n with
  | zero => exact absurd h0 hn
  | succ n ih =>
    by_cases h : p n
    · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
    · obtain ⟨t, ht, h1, h2⟩ := ih h
      exact ⟨t, by omega, h1, h2⟩

lemma not_modEq_of_lt {L : ℕ} {a b : ℤ} (h1 : 0 < a - b) (h2 : a - b < L) :
    ¬ a ≡ b [ZMOD L] := by
  intro h
  have hd : (L : ℤ) ∣ a - b := Int.ModEq.dvd h.symm
  have := Int.eq_zero_of_abs_lt_dvd hd (by rwa [abs_of_pos h1])
  omega

lemma mono_of_succ (x : ℤ → ℝ) (n : ℕ) (h : ∀ k : ℕ, k < n → x k < x (k + 1)) :
    ∀ i j : ℕ, i < j → j ≤ n → x i < x j := by
  intro i j hij hjn
  induction j with
  | zero => omega
  | succ j ih =>
    have hj := h j (by omega)
    push_cast
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact (ih h' (by omega)).trans hj
    · subst h'; exact hj

lemma escape (L : ℕ) (x : ℤ → ℝ)
    (hinj : ∀ i j, x i = x j ↔ i ≡ j [ZMOD L])
    (hnc : ∀ i j, ¬ i ≡ j [ZMOD L] → ¬ Sep (x i) (x (i + 1)) (x j) (x (j + 1)))
    (t : ℤ) (hlt : x t < x (t + 1)) (A : ℤ) (K : ℕ)
    (hin : x t < x A ∧ x A < x (t + 1)) (hout : x (A + K) < x t ∨ x (t + 1) < x (A + K))
    (hav : ∀ k : ℕ, k ≤ K → ¬ (A + k ≡ t [ZMOD L]) ∧ ¬ (A + k ≡ t + 1 [ZMOD L])) : False := by
  obtain ⟨j, hj, hpj, hpj1⟩ := exists_flip
    (fun j : ℕ => x t < x (A + j) ∧ x (A + j) < x (t + 1)) K
    (by simpa using hin) (by rintro ⟨h1, h2⟩; rcases hout with h | h <;> linarith)
  have hne1 : x (A + ((j + 1 : ℕ) : ℤ)) ≠ x t := by
    rw [Ne, hinj]; exact (hav (j + 1) hj).1
  have hne2 : x (A + ((j + 1 : ℕ) : ℤ)) ≠ x (t + 1) := by
    rw [Ne, hinj]; exact (hav (j + 1) hj).2
  apply hnc t (A + j) (fun h => (hav j hj.le).1 h.symm)
  have e : A + (j : ℤ) + 1 = A + ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [min_eq_left hlt.le]; exact hpj.1
  · rw [max_eq_right hlt.le]; exact hpj.2
  · rw [min_eq_left hlt.le, max_eq_right hlt.le, e]
    simp only [not_and_or, not_lt] at hpj1
    rcases hpj1 with h | h
    · exact Or.inl (lt_of_le_of_ne h hne1)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hne2))

/-- A cyclic sequence of distinct reals with pairwise non-crossing consecutive chords, rotated to
start at its minimum and oriented so that `x 1 ≤ x (-1)`, increases along `0, 1, …, L-1`. -/
lemma mono_core (L : ℕ) (x : ℤ → ℝ) (hL : 2 ≤ L)
    (hinj : ∀ i j, x i = x j ↔ i ≡ j [ZMOD L])
    (hnc : ∀ i j, ¬ i ≡ j [ZMOD L] → ¬ Sep (x i) (x (i + 1)) (x j) (x (j + 1)))
    (hmin : ∀ i, x 0 ≤ x i) (h1 : x 1 ≤ x (-1)) :
    ∀ n : ℕ, n + 1 < L → x n < x (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have hpre : ∀ i j : ℕ, i < j → j ≤ n → x i < x j :=
    mono_of_succ x n (fun k hk => ih k hk (by omega))
  have hne : x n ≠ x (n + 1) := by
    rw [Ne, hinj]; intro h
    exact not_modEq_of_lt (L := L) (a := (n : ℤ) + 1) (b := n) (by omega) (by omega) h.symm
  rcases lt_or_gt_of_ne hne with h | h
  · exact h
  exfalso
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have := hmin 1; simp at h; linarith
  set y := x ((n : ℤ) + 1) with hy
  have hy0 : x 0 < y := by
    refine lt_of_le_of_ne (hmin _) ?_
    rw [Ne, hinj]; intro h'
    exact not_modEq_of_lt (L := L) (a := (n : ℤ) + 1) (b := 0) (by omega) (by omega) h'.symm
  obtain ⟨t, ht, hpt, hpt1⟩ := exists_flip (fun i : ℕ => x i < y) n (by simpa using hy0)
    (not_lt.2 h.le)
  simp only [not_lt] at hpt1
  have hty : y < x ((t : ℤ) + 1) := by
    refine lt_of_le_of_ne (by exact_mod_cast hpt1) ?_
    rw [Ne, hy, hinj]; intro h'
    exact not_modEq_of_lt (L := L) (a := (n : ℤ) + 1) (b := (t : ℤ) + 1) (by omega)
      (by omega) h'
  have hlt : x t < x ((t : ℤ) + 1) := by
    have := hpre t (t + 1) (by omega) (by omega); exact_mod_cast this
  have hL0 : x (L : ℤ) = x 0 := by
    rw [hinj]; exact (Int.emod_self).trans (Int.zero_emod _).symm
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · -- chord `{x 0, x 1}`; escape towards `x (L-1) = x (-1)`
    have hL3 : 3 ≤ L := by omega
    have hLm : x ((L : ℤ) - 1) = x (-1) := by
      rw [hinj, Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
    have hout : x 1 < x ((L : ℤ) - 1) := by
      refine lt_of_le_of_ne (hLm ▸ h1) ?_
      rw [Ne, hinj]; intro h'
      exact not_modEq_of_lt (L := L) (a := (L : ℤ) - 1) (b := 1) (by omega) (by omega) h'.symm
    refine escape L x hinj hnc 0 (by simpa using hlt) ((n : ℤ) + 1) (L - n - 2) ⟨?_, ?_⟩ ?_ ?_
    · simpa using hy0
    · simpa using hty
    · right
      have e : (n : ℤ) + 1 + ((L - n - 2 : ℕ) : ℤ) = (L : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [e]; simpa using hout
    · intro k hk
      have hk' : (k : ℤ) ≤ L - n - 2 := by omega
      constructor
      · exact not_modEq_of_lt (by omega) (by omega)
      · exact not_modEq_of_lt (by omega) (by omega)
  · -- chord `{x t, x (t+1)}` with `t ≥ 1`; escape towards `x L = x 0`
    have h0t : x 0 < x t := by
      have := hpre 0 t ht0 (by omega); simpa using this
    refine escape L x hinj hnc t hlt ((n : ℤ) + 1) (L - n - 1) ⟨hpt, hty⟩ ?_ ?_
    · left
      have e : (n : ℤ) + 1 + ((L - n - 1 : ℕ) : ℤ) = (L : ℤ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [e, hL0]; exact h0t
    · intro k hk
      have hk' : (k : ℤ) ≤ L - n - 1 := by omega
      constructor
      · exact not_modEq_of_lt (by omega) (by omega)
      · exact not_modEq_of_lt (by omega) (by omega)

/-! ## Rotations and reflections of cycles -/
lemma cyc_rot {α β : Type*} {E : α → β → Prop} {L : ℕ} {C : ℤ → α} {F : ℤ → β}
    (h : Cyc E L C F) (m : ℤ) : Cyc E L (fun i => C (m + i)) (fun i => F (m + i)) := by
  obtain ⟨hL, h1, h2, hC, hF⟩ := h
  refine ⟨hL, fun i => h1 _, fun i => by
    show E (C (m + (i + 1))) (F (m + i)); rw [← add_assoc]; exact h2 _, ?_, ?_⟩
  · intro i j; rw [hC]; exact ⟨Int.ModEq.add_left_cancel' m, Int.ModEq.add_left m⟩
  · intro i j; rw [hF]; exact ⟨Int.ModEq.add_left_cancel' m, Int.ModEq.add_left m⟩

lemma modEq_sub_iff {L : ℕ} (c i j : ℤ) : (c - i ≡ c - j [ZMOD L]) ↔ i ≡ j [ZMOD L] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, show c - j - (c - i) = -(j - i) by ring, dvd_neg]

lemma cyc_refl {α β : Type*} {E : α → β → Prop} {L : ℕ} {C : ℤ → α} {F : ℤ → β}
    (h : Cyc E L C F) (m : ℤ) : Cyc E L (fun i => C (m - i)) (fun i => F (m - 1 - i)) := by
  obtain ⟨hL, h1, h2, hC, hF⟩ := h
  refine ⟨hL, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · show E (C (m - i)) (F (m - 1 - i))
    have := h2 (m - 1 - i); rwa [show m - 1 - i + 1 = m - i by ring] at this
  · show E (C (m - (i + 1))) (F (m - 1 - i))
    rw [show m - 1 - i = m - (i + 1) by ring]; exact h1 _
  · intro i j; rw [hC]; exact modEq_sub_iff m i j
  · intro i j; rw [hF]; exact modEq_sub_iff (m - 1) i j

/-! ## From a non-backtracking walk to a cycle -/
lemma inj_of_lt {γ : Type*} (g : ℕ → γ) (P : ℕ → Prop)
    (h : ∀ i j, i < j → P i → P j → g i ≠ g j) :
    ∀ i j, P i → P j → g i = g j → i = j := by
  intro i j hi hj he
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd he (h i j h' hi hj)
  · exact h'
  · exact absurd he.symm (h j i h' hj hi)

lemma emod_succ (L : ℕ) (hL : 0 < L) (i : ℤ) :
    (i + 1) % (L : ℤ) = if i % (L : ℤ) + 1 < L then i % (L : ℤ) + 1 else 0 := by
  have hd := Int.emod_add_mul_ediv i L
  have h0 := Int.emod_nonneg i (by omega : (L : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos i (by omega : (0 : ℤ) < L)
  have e : i + 1 = (i % L + 1) + L * (i / L) := by linarith
  rw [e, Int.add_mul_emod_self_left]
  split_ifs with h
  · exact Int.emod_eq_of_lt (by omega) h
  · rw [show i % (L : ℤ) + 1 = L by omega, Int.emod_self]

lemma cyc_of_walk {α β : Type*} [Fintype α] (E : α → β → Prop) (c : ℕ → α) (f : ℕ → β)
    (hE : ∀ n, E (c n) (f n)) (hE' : ∀ n, E (c (n + 1)) (f n))
    (hc : ∀ n, c (n + 1) ≠ c n) (hf : ∀ n, f (n + 1) ≠ f n) :
    ∃ L C F, Cyc E L C F := by
  obtain ⟨o, L, hL, hci, hfi, hcl⟩ : ∃ o L : ℕ, 2 ≤ L ∧
      (∀ i j, i < L → j < L → c (o + i) = c (o + j) → i = j) ∧
      (∀ i j, i < L → j < L → f (o + i) = f (o + j) → i = j) ∧ E (c o) (f (o + L - 1)) := by
    have hex : ∃ n, ∃ m < n, c m = c n ∨ f m = f n := by
      obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun i : Fin (Fintype.card α + 1) => c i) (by simp)
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h' | h'
      · exact ⟨j, i, h', Or.inl h⟩
      · exact ⟨i, j, h', Or.inl h.symm⟩
    obtain ⟨n, ⟨m, hmn, hm⟩, hmin⟩ : ∃ n, (∃ m < n, c m = c n ∨ f m = f n) ∧
        ∀ i j, i < j → j < n → c i ≠ c j ∧ f i ≠ f j := by
      refine ⟨Nat.find hex, Nat.find_spec hex, fun i j hij hjn => ?_⟩
      have := Nat.find_min hex hjn
      push_neg at this
      exact this i hij
    by_cases hA : ∃ m' < n, c m' = c n
    · obtain ⟨m', hm'n, hm'⟩ := hA
      have hn1 : n - 1 + 1 = n := by omega
      have hm'2 : m' ≠ n - 1 := by
        intro h; have := hc (n - 1); rw [hn1, ← h] at this; exact this hm'.symm
      refine ⟨m', n - m', by omega, ?_, ?_, ?_⟩
      · exact inj_of_lt (fun i => c (m' + i)) (· < n - m')
          (fun i j hij _ hj => (hmin _ _ (by omega) (by omega)).1)
      · exact inj_of_lt (fun i => f (m' + i)) (· < n - m')
          (fun i j hij _ hj => (hmin _ _ (by omega) (by omega)).2)
      · have := hE' (n - 1); rw [hn1, ← hm'] at this
        rwa [show m' + (n - m') - 1 = n - 1 by omega]
    · push_neg at hA
      have hfm : f m = f n := hm.resolve_left (hA m hmn)
      have hn1 : n - 1 + 1 = n := by omega
      have hm2 : m ≠ n - 1 := by
        intro h; have := hf (n - 1); rw [hn1, ← h] at this; exact this hfm.symm
      refine ⟨m + 1, n - m, by omega, ?_, ?_, ?_⟩
      · refine inj_of_lt (fun i => c (m + 1 + i)) (· < n - m) (fun i j hij _ hj => ?_)
        rcases Nat.lt_or_ge (m + 1 + j) n with h' | h'
        · exact (hmin _ _ (by omega) h').1
        · have e : m + 1 + j = n := by omega
          simp only [e]; exact hA _ (by omega)
      · refine inj_of_lt (fun i => f (m + 1 + i)) (· < n - m) (fun i j hij _ hj => ?_)
        rcases Nat.lt_or_ge (m + 1 + j) n with h' | h'
        · exact (hmin _ _ (by omega) h').2
        · have e : m + 1 + j = n := by omega
          simp only [e, ← hfm]; exact fun h => (hmin m _ (by omega) (by omega)).2 h.symm
      · rw [show m + 1 + (n - m) - 1 = n by omega, ← hfm]; exact hE' m
  have hL0 : (0 : ℤ) < L := by omega
  have hnn : ∀ i : ℤ, ((i % (L : ℤ)).toNat : ℤ) = i % L := fun i =>
    Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))
  have hlt : ∀ i : ℤ, (i % (L : ℤ)).toNat < L := fun i => by
    have := Int.emod_lt_of_pos i hL0; have := hnn i; omega
  refine ⟨L, fun i => c (o + (i % (L : ℤ)).toNat), fun i => f (o + (i % (L : ℤ)).toNat),
    hL, fun i => hE _, fun i => ?_, fun i j => ?_, fun i j => ?_⟩
  · have hs := emod_succ L (by omega) i
    have := hnn i; have := hlt i
    split_ifs at hs with h
    · have e : ((i + 1) % (L : ℤ)).toNat = (i % (L : ℤ)).toNat + 1 := by
        rw [hs]; omega
      simp only [e, ← add_assoc]; exact hE' _
    · have e : ((i + 1) % (L : ℤ)).toNat = 0 := by rw [hs]; rfl
      have e2 : o + (i % (L : ℤ)).toNat = o + L - 1 := by omega
      simp only [e, e2, add_zero]; exact hcl
  · constructor
    · intro h
      have := hci _ _ (hlt i) (hlt j) h
      show i % (L : ℤ) = j % (L : ℤ)
      rw [← hnn i, ← hnn j, this]
    · intro h
      have h' : i % (L : ℤ) = j % (L : ℤ) := h
      simp only [h']
  · constructor
    · intro h
      have := hfi _ _ (hlt i) (hlt j) h
      show i % (L : ℤ) = j % (L : ℤ)
      rw [← hnn i, ← hnn j, this]
    · intro h
      have h' : i % (L : ℤ) = j % (L : ℤ) := h
      simp only [h']

lemma exists_walk {α β : Type*} [Nonempty α] [Nonempty β] (E : α → β → Prop)
    (h1 : ∀ r v, E r v → ∃ v', v' ≠ v ∧ E r v') (h2 : ∀ r v, E r v → ∃ r', r' ≠ r ∧ E r' v)
    (r0 : α) (v0 : β) (h0 : E r0 v0) :
    ∃ (c : ℕ → α) (f : ℕ → β), (∀ n, E (c n) (f n)) ∧ (∀ n, E (c (n + 1)) (f n)) ∧
      (∀ n, c (n + 1) ≠ c n) ∧ (∀ n, f (n + 1) ≠ f n) := by
  choose! nv hnv using h1
  choose! nr hnr using h2
  let step : α × β → α × β := fun p => (nr p.1 p.2, nv (nr p.1 p.2) p.2)
  let seq : ℕ → α × β := fun n => step^[n] (r0, v0)
  have hseq : ∀ n, seq (n + 1) = step (seq n) := fun n =>
    Function.iterate_succ_apply' step n (r0, v0)
  have hE : ∀ n, E (seq n).1 (seq n).2 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [hseq]
      exact (hnv _ _ (hnr _ _ ih).2).2
  refine ⟨fun n => (seq n).1, fun n => (seq n).2, hE, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · simp only [hseq]; exact (hnr _ _ (hE n)).2
  · simp only [hseq]; exact (hnr _ _ (hE n)).1
  · simp only [hseq]; exact (hnv _ _ (hnr _ _ (hE n)).2).1

end SublinearChoresMMS.Dev.Rearr.PartCyc
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartCyc
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
/-! ## The LP setting -/
/-- A fractional edge of range `k`. -/
def Frac (Mv : Finset (Fin N)) (rk : Fin N → ℕ) (z : Fin N → Fin b → ℝ) (k : ℕ)
    (r : Fin N) (v : Fin b) : Prop :=
  r ∈ Mv ∧ rk r = k ∧ 0 < z r v ∧ z r v < 1

lemma sep_false_aux (s : Fin N → ℝ) (Mv : Finset (Fin N)) (rk : Fin N → ℕ)
    (z : Fin N → Fin b → ℝ)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v)
    (k : ℕ) (p p' q q' : Fin N) (u v : Fin b) (huv : u ≠ v)
    (hp : Frac Mv rk z k p u) (hp' : Frac Mv rk z k p' u)
    (hq : Frac Mv rk z k q v) (hq' : Frac Mv rk z k q' v) (hlt : s p < s p') :
    ¬ Sep (s p) (s p') (s q) (s q') := by
  rintro ⟨h1, h2, h3⟩
  rw [min_eq_left hlt.le] at h1 h3
  rw [max_eq_right hlt.le] at h2 h3
  obtain ⟨hpM, hpk, hpz, -⟩ := hp
  obtain ⟨hp'M, hp'k, hp'z, -⟩ := hp'
  obtain ⟨hqM, hqk, hqz, -⟩ := hq
  obtain ⟨hq'M, hq'k, hq'z, -⟩ := hq'
  have a := hord u v p hpM q hqM p' hp'M (hpk.trans hqk.symm) (hqk.trans hp'k.symm) h1 h2
    hpz hqz hp'z huv
  rcases h3 with h | h
  · have := hord v u q' hq'M p hpM q hqM (hq'k.trans hpk.symm) (hpk.trans hqk.symm) h h1
      hq'z hpz hqz huv.symm
    exact lt_asymm a this
  · have := hord v u q hqM p' hp'M q' hq'M (hqk.trans hp'k.symm) (hp'k.trans hq'k.symm) h2 h
      hqz hp'z hq'z huv.symm
    exact lt_asymm a this

lemma sep_false (s : Fin N → ℝ) (Mv : Finset (Fin N)) (rk : Fin N → ℕ)
    (z : Fin N → Fin b → ℝ)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v)
    (k : ℕ) (p p' q q' : Fin N) (u v : Fin b) (huv : u ≠ v)
    (hp : Frac Mv rk z k p u) (hp' : Frac Mv rk z k p' u)
    (hq : Frac Mv rk z k q v) (hq' : Frac Mv rk z k q' v) :
    ¬ Sep (s p) (s p') (s q) (s q') := by
  rcases lt_trichotomy (s p) (s p') with h | h | h
  · exact sep_false_aux s Mv rk z hord k p p' q q' u v huv hp hp' hq hq' h
  · rintro ⟨h1, h2, -⟩
    rw [h, min_self] at h1; rw [h, max_self] at h2; linarith
  · intro hs
    apply sep_false_aux s Mv rk z hord k p' p q q' u v huv hp' hp hq hq' h
    unfold Sep at hs ⊢
    rwa [min_comm, max_comm]

lemma final_of_cyc (s : Fin N → ℝ) (hs : StrictAnti s) (Mv : Finset (Fin N))
    (rk : Fin N → ℕ) (z : Fin N → Fin b → ℝ)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v)
    (r0 : Fin N) (L : ℕ) (C : ℤ → Fin N) (F : ℤ → Fin b)
    (hc : Cyc (Frac Mv rk z (rk r0)) L C F)
    (hmin : ∀ i, s (C 0) ≤ s (C i)) (h1 : s (C 1) ≤ s (C (-1))) :
    ∃ (len : ℕ) (a : Fin len → Fin N) (w : Fin len → Fin b), 2 ≤ len ∧
      StrictMono (fun j => s (a j)) ∧ Function.Injective w ∧
      (∀ j, a j ∈ Mv ∧ rk (a j) = rk r0) ∧
      (∀ j : Fin len, ∀ h : j.val + 1 < len,
        (0 < z (a j) (w j) ∧ z (a j) (w j) < 1) ∧
        (0 < z (a ⟨j.val + 1, h⟩) (w j) ∧ z (a ⟨j.val + 1, h⟩) (w j) < 1)) ∧
      (∀ j : Fin len, j.val + 1 = len →
        (0 < z (a j) (w j) ∧ z (a j) (w j) < 1) ∧
        (0 < z (a ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩) (w j) ∧
          z (a ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩) (w j) < 1)) := by
  obtain ⟨hL, hE, hE', hC, hF⟩ := hc
  have hinj : ∀ i j, s (C i) = s (C j) ↔ i ≡ j [ZMOD L] := fun i j =>
    hs.injective.eq_iff.trans (hC i j)
  have hnc : ∀ i j, ¬ i ≡ j [ZMOD L] →
      ¬ Sep (s (C i)) (s (C (i + 1))) (s (C j)) (s (C (j + 1))) := by
    intro i j hij
    exact sep_false s Mv rk z hord (rk r0) _ _ _ _ (F i) (F j)
      (fun h => hij ((hF i j).1 h)) (hE i) (hE' i) (hE j) (hE' j)
  have hmono := mono_core L (fun i => s (C i)) hL hinj hnc hmin h1
  have hsm := mono_of_succ (fun i => s (C i)) (L - 1)
    (fun k hk => hmono k (by omega))
  refine ⟨L, fun j => C (j.val : ℤ), fun j => F (j.val : ℤ), hL, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hsm i j hij (by omega)
  · intro i j hij
    have h := (hF _ _).1 hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact not_modEq_of_lt (L := L) (a := (j.val : ℤ)) (b := i.val) (by omega) (by omega)
        h.symm
    · exact not_modEq_of_lt (L := L) (a := (i.val : ℤ)) (b := j.val) (by omega) (by omega) h
  · intro j; exact ⟨(hE j).1, (hE j).2.1⟩
  · intro j hj
    have := hE' (j.val : ℤ)
    refine ⟨(hE j).2.2, ?_⟩
    simp only [Nat.cast_add, Nat.cast_one]
    exact this.2.2
  · intro j hj
    refine ⟨(hE j).2.2, ?_⟩
    have := hE' (j.val : ℤ)
    have e : C ((j.val : ℤ) + 1) = C 0 := by
      rw [hC]
      have : (j.val : ℤ) + 1 = L := by omega
      rw [this]; exact (Int.emod_self).trans (Int.zero_emod _).symm
    rw [e] at this
    simpa using this.2.2

theorem exists_monotone_cycle (s : Fin N → ℝ) (hs : StrictAnti s) (Mv : Finset (Fin N))
    (rk : Fin N → ℕ) (z : Fin N → Fin b → ℝ) (hz0 : ∀ r v, 0 ≤ z r v)
    (hzout : ∀ r ∉ Mv, ∀ v, z r v = 0) (hz1 : ∀ r ∈ Mv, ∑ v, z r v = 1)
    (hzc : ∀ v k, ∃ c : ℕ, ∑ r ∈ Mv.filter (fun r => rk r = k), z r v = c)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v)
    (r0 : Fin N) (v0 : Fin b) (h0 : 0 < z r0 v0) (h1 : z r0 v0 < 1) :
    ∃ (len : ℕ) (a : Fin len → Fin N) (w : Fin len → Fin b), 2 ≤ len ∧
      StrictMono (fun j => s (a j)) ∧ Function.Injective w ∧
      (∀ j, a j ∈ Mv ∧ rk (a j) = rk r0) ∧
      (∀ j : Fin len, ∀ h : j.val + 1 < len,
        (0 < z (a j) (w j) ∧ z (a j) (w j) < 1) ∧
        (0 < z (a ⟨j.val + 1, h⟩) (w j) ∧ z (a ⟨j.val + 1, h⟩) (w j) < 1)) ∧
      (∀ j : Fin len, j.val + 1 = len →
        (0 < z (a j) (w j) ∧ z (a j) (w j) < 1) ∧
        (0 < z (a ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩) (w j) ∧ z (a ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩) (w j) < 1)) := by
  have hr0 : r0 ∈ Mv := by
    by_contra h; have := hzout r0 h v0; linarith
  have hle1 : ∀ r ∈ Mv, ∀ v, z r v ≤ 1 := fun r hr v => by
    rw [← hz1 r hr]; exact Finset.single_le_sum (fun v _ => hz0 r v) (mem_univ v)
  have hitem : ∀ r v, Frac Mv rk z (rk r0) r v → ∃ v', v' ≠ v ∧ Frac Mv rk z (rk r0) r v' := by
    rintro r v ⟨hr, hk, hp, hl⟩
    have hs1 := hz1 r hr
    rw [← Finset.add_sum_erase _ _ (mem_univ v)] at hs1
    have hpos : ∃ v' ∈ univ.erase v, 0 < z r v' := by
      by_contra hc; push_neg at hc
      have := Finset.sum_nonpos hc; linarith
    obtain ⟨v', hv', hpv'⟩ := hpos
    refine ⟨v', ne_of_mem_erase hv', hr, hk, hpv', ?_⟩
    have := Finset.single_le_sum (fun v _ => hz0 r v) hv'
    linarith
  have hbin : ∀ r v, Frac Mv rk z (rk r0) r v → ∃ r', r' ≠ r ∧ Frac Mv rk z (rk r0) r' v := by
    rintro r v ⟨hr, hk, hp, hl⟩
    by_contra hc; push_neg at hc
    have hrS : r ∈ Mv.filter (fun r' => rk r' = rk r0) := mem_filter.2 ⟨hr, hk⟩
    obtain ⟨c, hc'⟩ := hzc v (rk r0)
    rw [← Finset.add_sum_erase _ _ hrS] at hc'
    have h01 : ∀ r' ∈ (Mv.filter (fun r' => rk r' = rk r0)).erase r,
        z r' v = if z r' v = 1 then 1 else 0 := by
      intro r' hr'
      have hr'S := mem_filter.1 (mem_of_mem_erase hr')
      have hne := ne_of_mem_erase hr'
      have hnf := hc r' hne
      split_ifs with h1'
      · exact h1'
      · have h0' := hz0 r' v
        have h1'' := hle1 r' hr'S.1 v
        by_contra h0''
        exact hnf ⟨hr'S.1, hr'S.2, lt_of_le_of_ne h0' (Ne.symm h0''), lt_of_le_of_ne h1'' h1'⟩
    rw [Finset.sum_congr rfl h01, Finset.sum_boole] at hc'
    set m := (((Mv.filter (fun r' => rk r' = rk r0)).erase r).filter fun r' => z r' v = 1).card
    have hz : z r v = (((c : ℤ) - m : ℤ) : ℝ) := by push_cast; linarith
    have a1 : (0 : ℝ) < (((c : ℤ) - m : ℤ) : ℝ) := hz ▸ hp
    have a2 : (((c : ℤ) - m : ℤ) : ℝ) < 1 := hz ▸ hl
    have b1 : (0 : ℤ) < (c : ℤ) - m := by exact_mod_cast a1
    have b2 : (c : ℤ) - m < 1 := by exact_mod_cast a2
    omega
  have : Nonempty (Fin N) := ⟨r0⟩
  have : Nonempty (Fin b) := ⟨v0⟩
  obtain ⟨c, f, hE, hE', hc, hf⟩ :=
    exists_walk (Frac Mv rk z (rk r0)) hitem hbin r0 v0 ⟨hr0, rfl, h0, h1⟩
  obtain ⟨L, C, F, hcyc⟩ := cyc_of_walk _ c f hE hE' hc hf
  have hL := hcyc.1
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image (Finset.range L) (fun i : ℕ => s (C i))
    ⟨0, by simp; omega⟩
  have hmin : ∀ i : ℤ, s (C m) ≤ s (C i) := by
    intro i
    have hnn : ((i % (L : ℤ)).toNat : ℤ) = i % L :=
      Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))
    have hlt : (i % (L : ℤ)).toNat < L := by
      have := Int.emod_lt_of_pos i (by omega : (0 : ℤ) < L); omega
    have e : C i = C ((i % (L : ℤ)).toNat : ℕ) := by
      rw [hcyc.2.2.2.1, hnn]; exact (Int.mod_modEq i L).symm
    rw [e]; exact hm _ (Finset.mem_range.2 hlt)
  by_cases hdir : s (C (m + 1)) ≤ s (C (m + -1))
  · exact final_of_cyc s hs Mv rk z hord r0 L _ _ (cyc_rot hcyc m)
      (fun i => by simpa using hmin (m + i)) hdir
  · refine final_of_cyc s hs Mv rk z hord r0 L _ _ (cyc_refl hcyc m)
      (fun i => by simpa using hmin (m - i)) ?_
    simp only [sub_neg_eq_add]
    rw [show (m : ℤ) - 1 = m + -1 by ring]
    exact (not_le.1 hdir).le

end SublinearChoresMMS.Dev.Rearr.PartCyc
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
alias exists_monotone_cycle := SublinearChoresMMS.Dev.Rearr.PartCyc.exists_monotone_cycle

end SublinearChoresMMS.Dev.Rearr
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartRound
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
/-- Fractional value. -/
def Fr (x : ℝ) : Prop := 0 < x ∧ x < 1

/-! ## Cyclic successor -/
/-- Cyclic successor on `Fin len`. -/
def nxt {len : ℕ} (h : 2 ≤ len) (j : Fin len) : Fin len :=
  ⟨if j.val + 1 < len then j.val + 1 else 0, by split_ifs <;> omega⟩

lemma nxt_val {len : ℕ} (h : 2 ≤ len) (j : Fin len) :
    (nxt h j).val = if j.val + 1 < len then j.val + 1 else 0 := rfl

lemma nxt_inj {len : ℕ} (h : 2 ≤ len) : Function.Injective (nxt h) := by
  intro i j hij
  have := congrArg Fin.val hij
  rw [nxt_val, nxt_val] at this
  ext; split_ifs at this <;> omega

lemma nxt_ne {len : ℕ} (h : 2 ≤ len) (j : Fin len) : nxt h j ≠ j := by
  intro e
  have := congrArg Fin.val e
  rw [nxt_val] at this
  split_ifs at this <;> omega

lemma sum_nxt {len : ℕ} (h : 2 ≤ len) (f : Fin len → ℝ) : ∑ j, f (nxt h j) = ∑ j, f j :=
  Function.Bijective.sum_comp (Finite.injective_iff_bijective.mp (nxt_inj h)) f

/-! ## The update vector of a cycle -/
/-- Update along the cycle: bin `w j` gains item `a j` and loses item `a (nxt j)`. -/
def dl {len : ℕ} (h : 2 ≤ len) (a : Fin len → Fin N) (w : Fin len → Fin b)
    (r : Fin N) (v : Fin b) : ℝ :=
  ∑ j, ((if a j = r ∧ w j = v then 1 else 0) - (if a (nxt h j) = r ∧ w j = v then 1 else 0))

lemma dl_wsum {len : ℕ} (h : 2 ≤ len) (a : Fin len → Fin N) (w : Fin len → Fin b) (v : Fin b)
    (A : Finset (Fin N)) (f : Fin N → ℝ) :
    ∑ r ∈ A, f r * dl h a w r v = ∑ j, if w j = v then
      ((if a j ∈ A then f (a j) else 0) - (if a (nxt h j) ∈ A then f (a (nxt h j)) else 0))
      else 0 := by
  simp only [dl, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  by_cases hv : w j = v
  · simp [hv, mul_sub, sum_sub_distrib]
  · simp [hv]

lemma dl_supply {len : ℕ} (h : 2 ≤ len) (a : Fin len → Fin N) (w : Fin len → Fin b)
    (r : Fin N) : ∑ v, dl h a w r v = 0 := by
  simp only [dl]
  rw [sum_comm]
  have : ∀ j : Fin len, ∑ v, ((if a j = r ∧ w j = v then (1 : ℝ) else 0) -
      (if a (nxt h j) = r ∧ w j = v then 1 else 0)) =
      (if a j = r then 1 else 0) - (if a (nxt h j) = r then 1 else 0) := by
    intro j
    simp [sum_sub_distrib, ite_and]
  rw [sum_congr rfl fun j _ => this j, sum_sub_distrib,
    sum_nxt h (fun j => if a j = r then (1 : ℝ) else 0), sub_self]

lemma sum_w_single {len : ℕ} {w : Fin len → Fin b} (hw : Function.Injective w)
    (g : Fin len → ℝ) (j : Fin len) : ∑ i, (if w i = w j then g i else 0) = g j := by
  rw [sum_eq_single j]
  · simp
  · intro i _ hi; simp [hw.ne hi]
  · simp

lemma dl_at {len : ℕ} (h : 2 ≤ len) (a : Fin len → Fin N) {w : Fin len → Fin b}
    (hw : Function.Injective w) (j : Fin len) (r : Fin N) :
    dl h a w r (w j) = (if a j = r then 1 else 0) - (if a (nxt h j) = r then 1 else 0) := by
  have := sum_w_single hw (fun i => (if a i = r then (1 : ℝ) else 0) -
    (if a (nxt h i) = r then 1 else 0)) j
  rw [← this]
  unfold dl
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : w i = w j <;> simp [hi]

lemma dl_off {len : ℕ} (h : 2 ≤ len) (a : Fin len → Fin N) (w : Fin len → Fin b) (v : Fin b)
    (hv : ∀ j, w j ≠ v) (r : Fin N) : dl h a w r v = 0 := by
  simp [dl, hv]

/-! ## The invariant subspace -/
/-- Directions supported on fractional entries of `z`, with homogeneous supply and counts. -/
def W0 (Mv : Finset (Fin N)) (rk : Fin N → ℕ) (z : Fin N → Fin b → ℝ) :
    Submodule ℝ (Fin N → Fin b → ℝ) where
  carrier := {δ | (∀ r v, δ r v ≠ 0 → Fr (z r v)) ∧ (∀ r, ∑ v, δ r v = 0) ∧
    (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0)}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨fun r v h => ?_, fun r => ?_, fun v k => ?_⟩
    · by_cases hx : x r v = 0
      · exact hy1 r v (by simpa [hx] using h)
      · exact hx1 r v hx
    · simp [sum_add_distrib, hx2, hy2]
    · simp [sum_add_distrib, hx3, hy3]
  zero_mem' := by simp
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    refine ⟨fun r v h => hx1 r v ?_, fun r => ?_, fun v k => ?_⟩
    · intro h0; apply h; simp [h0]
    · simp [← mul_sum, hx2]
    · simp [← mul_sum, hx3]

lemma finrank_le (hb : 0 < b) (s : Fin N → ℝ) (Mv : Finset (Fin N)) (rk : Fin N → ℕ)
    (z : Fin N → Fin b → ℝ)
    (hbasic : ∀ δ : Fin N → Fin b → ℝ, (∀ r v, δ r v ≠ 0 → 0 < z r v ∧ z r v < 1) →
      (∀ r, ∑ v, δ r v = 0) →
      (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0) →
      (∀ v, ∑ r, s r * δ r v = 0) → δ = 0)
    (S : Submodule ℝ (Fin N → Fin b → ℝ)) (hS : S ≤ W0 Mv rk z) :
    Module.finrank ℝ S ≤ b - 1 := by
  let T : (Fin b → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ v, x v
      map_add' := by intros; simp [sum_add_distrib]
      map_smul' := by intros; simp [mul_sum] }
  let ℓ : (Fin N → Fin b → ℝ) →ₗ[ℝ] (Fin b → ℝ) :=
    { toFun := fun x v => ∑ r, s r * x r v
      map_add' := by intros; funext v; simp [mul_add, sum_add_distrib]
      map_smul' := by intros; funext v; simp [mul_sum, mul_left_comm] }
  have hmapT : ∀ x : S, (ℓ.comp S.subtype) x ∈ LinearMap.ker T := by
    rintro ⟨x, hx⟩
    have hW := hS hx
    rw [LinearMap.mem_ker]
    show ∑ v, ∑ r, s r * x r v = 0
    rw [sum_comm]
    simp [← mul_sum, hW.2.1]
  let f : S →ₗ[ℝ] LinearMap.ker T := LinearMap.codRestrict (LinearMap.ker T) (ℓ.comp S.subtype) hmapT
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hfx
    have h0 : ℓ x = 0 := congrArg Subtype.val hfx
    have hW := hS hx
    have := hbasic x hW.1 hW.2.1 hW.2.2 (fun v => congrFun h0 v)
    exact Subtype.ext this
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  have h3 : Module.finrank ℝ (LinearMap.range T) = 1 := by
    have : LinearMap.range T = ⊤ := LinearMap.range_eq_top.mpr fun c =>
      ⟨fun v => if v = ⟨0, hb⟩ then c else 0, by simp [T]⟩
    rw [this, finrank_top, Module.finrank_self]
  rw [Module.finrank_fin_fun] at h2
  omega

/-! ## The rounding invariant -/
/-- State of the rounding after some updates: current matrix `z'`, span `S` of the updates, and
the gain counters `u`. -/
structure Inv (s : Fin N → ℝ) (Mv : Finset (Fin N)) (rk : Fin N → ℕ) (W : ℝ)
    (z z' : Fin N → Fin b → ℝ) (S : Submodule ℝ (Fin N → Fin b → ℝ)) (u : Fin b → ℕ → ℕ) :
    Prop where
  nn : ∀ r v, 0 ≤ z' r v
  keep : ∀ r v, ¬ Fr (z r v) → z' r v = z r v
  sup : ∀ r ∈ Mv, ∑ v, z' r v = 1
  cnt : ∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), z' r v =
    ∑ r ∈ Mv.filter (fun r => rk r = k), z r v
  sw : S ≤ W0 Mv rk z
  sfr : ∀ x ∈ S, x ≠ 0 → ∃ r v, x r v ≠ 0 ∧ ¬ Fr (z' r v)
  rank : ∑ v, ∑ k ∈ Mv.image rk, u v k = Module.finrank ℝ S
  thr : ∀ v k (θ : ℝ), ∑ r ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r), z' r v ≤
    ∑ r ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r), z r v + u v k
  ld : ∀ v, ∑ r ∈ Mv, s r * z' r v - ∑ r ∈ Mv, s r * z r v ≤
    ((∑ k ∈ Mv.image rk, u v k : ℕ) : ℝ) * W

lemma Inv.pos {s : Fin N → ℝ} {Mv : Finset (Fin N)} {rk : Fin N → ℕ} {W : ℝ}
    {z z' : Fin N → Fin b → ℝ} {S : Submodule ℝ (Fin N → Fin b → ℝ)} {u : Fin b → ℕ → ℕ}
    (I : Inv s Mv rk W z z' S u) (r : Fin N) (v : Fin b) (h : 0 < z' r v) : 0 < z r v := by
  by_cases hF : Fr (z r v)
  · exact hF.1
  · rwa [← I.keep r v hF]

/-- Number of fractional entries. -/
def fcount (x : Fin N → Fin b → ℝ) : ℕ :=
  (univ.filter fun p : Fin N × Fin b => Fr (x p.1 p.2)).card

lemma step (s : Fin N → ℝ) (hs : StrictAnti s) (Mv : Finset (Fin N)) (rk : Fin N → ℕ)
    (W : ℝ) (hW : ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, rk r1 = rk r2 → s r1 - s r2 ≤ W)
    (z : Fin N → Fin b → ℝ) (hzout : ∀ r ∉ Mv, ∀ v, z r v = 0)
    (hzc : ∀ v k, ∃ c : ℕ, ∑ r ∈ Mv.filter (fun r => rk r = k), z r v = c)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v)
    (z' : Fin N → Fin b → ℝ) (S : Submodule ℝ (Fin N → Fin b → ℝ)) (u : Fin b → ℕ → ℕ)
    (I : Inv s Mv rk W z z' S u) (r0 : Fin N) (v0 : Fin b) (hf : Fr (z' r0 v0)) :
    ∃ z'' S' u', Inv s Mv rk W z z'' S' u' ∧ fcount z'' < fcount z' := by
  have hout' : ∀ r ∉ Mv, ∀ v, z' r v = 0 := fun r hr v => by
    have : ¬ Fr (z r v) := by simp [Fr, hzout r hr v]
    rw [I.keep r v this, hzout r hr v]
  have hzc' : ∀ v k, ∃ c : ℕ, ∑ r ∈ Mv.filter (fun r => rk r = k), z' r v = c := fun v k => by
    rw [I.cnt v k]; exact hzc v k
  have hord' : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z' r1 u → 0 < z' r2 v → 0 < z' r3 u → u ≠ v → u < v :=
    fun u v r1 h1 r2 h2 r3 h3 e1 e2 l1 l2 p1 p2 p3 ne =>
      hord u v r1 h1 r2 h2 r3 h3 e1 e2 l1 l2 (I.pos _ _ p1) (I.pos _ _ p2) (I.pos _ _ p3) ne
  have hFrz : ∀ r v, Fr (z' r v) → Fr (z r v) := fun r v h => by
    by_contra hc; rw [I.keep r v hc] at h; exact hc h
  have hr0 : r0 ∈ Mv := by
    by_contra hc; have := hout' r0 hc v0; rw [this] at hf; exact lt_irrefl _ hf.1
  obtain ⟨len, a, w, hlen, hmono, hw, hmem, hedge, hlast⟩ :=
    SublinearChoresMMS.Dev.Rearr.exists_monotone_cycle s hs Mv rk z' I.nn hout' I.sup hzc'
      hord' r0 v0 hf.1 hf.2
  have ha : Function.Injective a := fun i j e => hmono.injective (by simp [e])
  have hE : ∀ j, Fr (z' (a j) (w j)) ∧ Fr (z' (a (nxt hlen j)) (w j)) := by
    intro j
    by_cases hj : j.val + 1 < len
    · have : nxt hlen j = ⟨j.val + 1, hj⟩ := Fin.ext (by simp [nxt_val, hj])
      rw [this]; exact hedge j hj
    · have hj' : j.val + 1 = len := by omega
      have : nxt hlen j = ⟨0, by omega⟩ := Fin.ext (by simp [nxt_val, hj])
      rw [this]; exact hlast j hj'
  have hstep : ∀ j : Fin len, j.val + 1 < len → s (a j) < s (a (nxt hlen j)) := by
    intro j hj
    apply hmono
    show j < nxt hlen j
    rw [Fin.lt_iff_val_lt_val, nxt_val]; simp [hj]
  let jl : Fin len := ⟨len - 1, by omega⟩
  have hjl : ∀ j : Fin len, ¬ j.val + 1 < len → j = jl := fun j hj => Fin.ext (by simp [jl]; omega)
  have hWnn : 0 ≤ W := by
    have := hW (a jl) (hmem jl).1 (a jl) (hmem jl).1 rfl; simpa using this
  -- values of the update
  have hδval : ∀ r v, dl hlen a w r v ≠ 0 →
      (dl hlen a w r v = 1 ∨ dl hlen a w r v = -1) ∧ Fr (z' r v) := by
    intro r v h
    by_cases hv : ∃ j, w j = v
    · obtain ⟨j, rfl⟩ := hv
      rw [dl_at hlen a hw j r] at h ⊢
      have hne : a (nxt hlen j) ≠ a j := fun e => nxt_ne hlen j (ha e)
      by_cases h1 : a j = r
      · subst h1
        exact ⟨Or.inl (by simp [hne]), (hE j).1⟩
      · by_cases h2 : a (nxt hlen j) = r
        · subst h2
          exact ⟨Or.inr (by simp [h1]), (hE j).2⟩
        · simp [h1, h2] at h
    · push_neg at hv; exact absurd (dl_off hlen a w v hv r) h
  have hδfr : ∀ r v, dl hlen a w r v ≠ 0 → Fr (z' r v) := fun r v h => (hδval r v h).2
  have hcnt : ∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), dl hlen a w r v = 0 := by
    intro v k
    have := dl_wsum hlen a w v (Mv.filter (fun r => rk r = k)) (fun _ => 1)
    simp only [one_mul] at this
    rw [this]
    apply sum_eq_zero
    intro j _
    have h1 := hmem j
    have h2 := hmem (nxt hlen j)
    have e : (a j ∈ Mv.filter (fun r => rk r = k)) ↔
        (a (nxt hlen j) ∈ Mv.filter (fun r => rk r = k)) := by
      simp [h1.1, h2.1, h1.2, h2.2]
    by_cases hj : a j ∈ Mv.filter (fun r => rk r = k)
    · simp [hj, e.mp hj]
    · simp [hj, mt e.mpr hj]
  have hδW : dl hlen a w ∈ W0 Mv rk z :=
    ⟨fun r v h => hFrz r v (hδfr r v h), dl_supply hlen a w, hcnt⟩
  have j0 : Fin len := ⟨0, by omega⟩
  have hd0 : dl hlen a w (a j0) (w j0) = 1 := by
    rw [dl_at hlen a hw]
    have hne : a (nxt hlen j0) ≠ a j0 := fun e => nxt_ne hlen j0 (ha e)
    simp [hne]
  have hne : dl hlen a w ≠ 0 := by
    intro h; rw [h] at hd0; simp at hd0
  -- step size
  let g : Fin N × Fin b → ℝ := fun p =>
    if 0 < dl hlen a w p.1 p.2 then 1 - z' p.1 p.2 else z' p.1 p.2
  let E := univ.filter (fun p : Fin N × Fin b => dl hlen a w p.1 p.2 ≠ 0)
  have hEne : E.Nonempty := ⟨(a j0, w j0), by simp [E, hd0]⟩
  obtain ⟨ps, hpE, hpmin⟩ := Finset.exists_min_image E g hEne
  have hpE' : dl hlen a w ps.1 ps.2 ≠ 0 := (mem_filter.mp hpE).2
  have hgpos : ∀ p ∈ E, 0 < g p ∧ g p ≤ 1 := by
    intro p hp
    have hp' : dl hlen a w p.1 p.2 ≠ 0 := (mem_filter.mp hp).2
    obtain ⟨-, hF⟩ := hδval _ _ hp'
    simp only [g]
    split_ifs <;> constructor <;> linarith [hF.1, hF.2]
  set ε := g ps with hε
  have hε0 : 0 < ε := (hgpos ps hpE).1
  have hε1 : ε ≤ 1 := (hgpos ps hpE).2
  let z'' : Fin N → Fin b → ℝ := fun r v => z' r v + ε * dl hlen a w r v
  have hz''0 : ∀ r v, dl hlen a w r v = 0 → z'' r v = z' r v := fun r v h => by simp [z'', h]
  have hz''nn : ∀ r v, 0 ≤ z'' r v := by
    intro r v
    by_cases h : dl hlen a w r v = 0
    · rw [hz''0 r v h]; exact I.nn r v
    · have hp : (r, v) ∈ E := by simp [E, h]
      have hle := hpmin _ hp
      obtain ⟨h1 | h1, hF⟩ := hδval r v h
      · simp only [z'', h1]; linarith [I.nn r v]
      · simp only [g, h1] at hle
        simp only [z'', h1]
        have : ¬ (0 : ℝ) < -1 := by norm_num
        simp only [this, if_false] at hle
        linarith
  have hstar : ¬ Fr (z'' ps.1 ps.2) := by
    obtain ⟨h1 | h1, -⟩ := hδval _ _ hpE'
    · have : z'' ps.1 ps.2 = 1 := by
        simp only [z'', hε, g, h1]; norm_num
      rw [this]; simp [Fr]
    · have : z'' ps.1 ps.2 = 0 := by
        simp only [z'', hε, g, h1]; norm_num
      rw [this]; simp [Fr]
  -- indicator for the last bin
  have hk0 : rk r0 ∈ Mv.image rk := mem_image_of_mem rk hr0
  let u' : Fin b → ℕ → ℕ := fun v k => u v k + if v = w jl ∧ k = rk r0 then 1 else 0
  have hu'sum : ∀ v, ∑ k ∈ Mv.image rk, u' v k =
      ∑ k ∈ Mv.image rk, u v k + if v = w jl then 1 else 0 := by
    intro v
    simp only [u', sum_add_distrib]
    by_cases hv : v = w jl <;> simp [hv, hk0]
  -- rank
  have hnot : dl hlen a w ∉ S := fun hm => by
    obtain ⟨r, v, h1, h2⟩ := I.sfr _ hm hne
    exact h2 (hδfr r v h1)
  have hrank : Module.finrank ℝ ↥(S ⊔ Submodule.span ℝ {dl hlen a w}) =
      Module.finrank ℝ S + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span ℝ {dl hlen a w})
    have h2 : S ⊓ Submodule.span ℝ {dl hlen a w} = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxS, hxD⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxD
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd ((Submodule.smul_mem_iff S hc).mp hxS) hnot
    rw [h2, finrank_bot, finrank_span_singleton hne] at h1
    omega
  -- threshold bound for one update
  have hthr1 : ∀ v k (θ : ℝ), ∑ r ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r), dl hlen a w r v ≤
      if v = w jl ∧ k = rk r0 then 1 else 0 := by
    intro v k θ
    have := dl_wsum hlen a w v (Mv.filter (fun r => rk r = k ∧ θ ≤ s r)) (fun _ => 1)
    simp only [one_mul] at this
    rw [this]
    have hind : (0 : ℝ) ≤ if v = w jl ∧ k = rk r0 then 1 else 0 := by split_ifs <;> norm_num
    by_cases hv : ∃ j, w j = v
    · obtain ⟨j, rfl⟩ := hv
      rw [sum_w_single hw (fun j => (if a j ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r) then
        (1 : ℝ) else 0) - (if a (nxt hlen j) ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r) then
        1 else 0)) j]
      by_cases hj : j.val + 1 < len
      · have himp : a j ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r) →
            a (nxt hlen j) ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r) := by
          intro hm
          simp only [mem_filter] at hm ⊢
          refine ⟨(hmem _).1, ?_, le_trans hm.2.2 (hstep j hj).le⟩
          rw [(hmem _).2, ← (hmem j).2]; exact hm.2.1
        by_cases h1 : a j ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r)
        · simp [h1, himp h1, hind]
        · simp only [h1, if_false]
          split_ifs <;> linarith
      · have := hjl j hj
        subst this
        by_cases h1 : a jl ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r)
        · have hk : k = rk r0 := by
            simp only [mem_filter] at h1; rw [← h1.2.1, (hmem jl).2]
          simp only [h1, if_true, hk, and_self]
          split_ifs <;> norm_num
        · simp only [h1, if_false]
          split_ifs <;> linarith
    · push_neg at hv
      simp [hv, hind]
  -- load bound for one update
  have hld1 : ∀ v, ∑ r ∈ Mv, s r * dl hlen a w r v ≤ (if v = w jl then 1 else 0) * W := by
    intro v
    rw [dl_wsum]
    have hind : 0 ≤ (if v = w jl then (1 : ℝ) else 0) * W := by
      split_ifs <;> simp [hWnn]
    by_cases hv : ∃ j, w j = v
    · obtain ⟨j, rfl⟩ := hv
      rw [sum_w_single hw (fun j => (if a j ∈ Mv then s (a j) else 0) -
        (if a (nxt hlen j) ∈ Mv then s (a (nxt hlen j)) else 0)) j]
      simp only [(hmem j).1, (hmem (nxt hlen j)).1, if_true]
      by_cases hj : j.val + 1 < len
      · linarith [hstep j hj]
      · have := hjl j hj
        subst this
        simp only [if_true, one_mul]
        exact hW _ (hmem jl).1 _ (hmem _).1 (by rw [(hmem jl).2, (hmem _).2])
    · push_neg at hv
      rw [sum_eq_zero (fun j _ => by simp [hv j])]; exact hind
  refine ⟨z'', S ⊔ Submodule.span ℝ {dl hlen a w}, u', ?_, ?_⟩
  · refine
      { nn := hz''nn
        keep := ?_
        sup := ?_
        cnt := ?_
        sw := ?_
        sfr := ?_
        rank := ?_
        thr := ?_
        ld := ?_ }
    · intro r v hF
      have h0 : dl hlen a w r v = 0 := by
        by_contra h; exact hF (hFrz r v (hδfr r v h))
      rw [hz''0 r v h0, I.keep r v hF]
    · intro r hr
      simp only [z'', sum_add_distrib, ← mul_sum, dl_supply, mul_zero, add_zero]
      exact I.sup r hr
    · intro v k
      simp only [z'', sum_add_distrib, ← mul_sum, hcnt, mul_zero, add_zero]
      exact I.cnt v k
    · exact sup_le I.sw ((Submodule.span_le).mpr (Set.singleton_subset_iff.mpr hδW))
    · intro x hx hx0
      obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hd
      by_cases hy0 : y = 0
      · subst hy0
        have hc : c ≠ 0 := by rintro rfl; simp at hx0
        exact ⟨ps.1, ps.2, by simp [hc, hpE'], hstar⟩
      · obtain ⟨r, v, h1, h2⟩ := I.sfr y hy hy0
        have hd0 : dl hlen a w r v = 0 := by by_contra h; exact h2 (hδfr r v h)
        exact ⟨r, v, by simp [hd0, h1], by rw [hz''0 r v hd0]; exact h2⟩
    · rw [hrank, ← I.rank]
      simp only [hu'sum, sum_add_distrib]
      simp
    · intro v k θ
      have h1 := I.thr v k θ
      have h2 := hthr1 v k θ
      simp only [z'', sum_add_distrib, ← mul_sum]
      have h3 : ε * ∑ r ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r), dl hlen a w r v ≤
          if v = w jl ∧ k = rk r0 then 1 else 0 := by
        have hind : (0 : ℝ) ≤ if v = w jl ∧ k = rk r0 then 1 else 0 := by split_ifs <;> norm_num
        have hind1 : (if v = w jl ∧ k = rk r0 then (1 : ℝ) else 0) ≤ 1 := by
          split_ifs <;> norm_num
        nlinarith
      simp only [u']
      push_cast
      linarith
    · intro v
      have h1 := I.ld v
      have h2 := hld1 v
      simp only [z'', mul_add, sum_add_distrib, mul_left_comm _ ε, ← mul_sum]
      have h3 : ε * ∑ r ∈ Mv, s r * dl hlen a w r v ≤ (if v = w jl then 1 else 0) * W := by
        have hind : 0 ≤ (if v = w jl then (1 : ℝ) else 0) * W := by
          split_ifs <;> simp [hWnn]
        nlinarith
      rw [hu'sum v]
      push_cast at h1 ⊢
      split_ifs at h3 ⊢ <;> linarith
  · unfold fcount
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨ps, ?_, ?_⟩
      · simpa using (hδfr _ _ hpE')
      · simpa using hstar
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      by_contra hc
      have h0 : dl hlen a w p.1 p.2 = 0 := by by_contra h; exact hc (hδfr _ _ h)
      rw [hz''0 _ _ h0] at hp
      exact hc hp

lemma reach (s : Fin N → ℝ) (hs : StrictAnti s) (Mv : Finset (Fin N)) (rk : Fin N → ℕ)
    (W : ℝ) (hW : ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, rk r1 = rk r2 → s r1 - s r2 ≤ W)
    (z : Fin N → Fin b → ℝ) (hzout : ∀ r ∉ Mv, ∀ v, z r v = 0)
    (hzc : ∀ v k, ∃ c : ℕ, ∑ r ∈ Mv.filter (fun r => rk r = k), z r v = c)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v) :
    ∀ n (z' : Fin N → Fin b → ℝ) (S : Submodule ℝ (Fin N → Fin b → ℝ)) (u : Fin b → ℕ → ℕ),
      fcount z' = n → Inv s Mv rk W z z' S u →
      ∃ z'' S'' u'', Inv s Mv rk W z z'' S'' u'' ∧ ∀ r v, ¬ Fr (z'' r v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z' S u hn I
  by_cases h : ∃ r v, Fr (z' r v)
  · obtain ⟨r0, v0, hf⟩ := h
    obtain ⟨z'', S', u', I', hlt⟩ :=
      step s hs Mv rk W hW z hzout hzc hord z' S u I r0 v0 hf
    exact ih _ (hn ▸ hlt) z'' S' u' rfl I'
  · push_neg at h
    exact ⟨z', S, u, I, h⟩

theorem round (hb : 0 < b) (s : Fin N → ℝ) (hs : StrictAnti s) (Mv : Finset (Fin N)) (rk : Fin N → ℕ)
    (W : ℝ) (hW : ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, rk r1 = rk r2 → s r1 - s r2 ≤ W)
    (z : Fin N → Fin b → ℝ) (hz0 : ∀ r v, 0 ≤ z r v) (hzout : ∀ r ∉ Mv, ∀ v, z r v = 0)
    (hz1 : ∀ r ∈ Mv, ∑ v, z r v = 1)
    (hzc : ∀ v k, ∃ c : ℕ, ∑ r ∈ Mv.filter (fun r => rk r = k), z r v = c)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, ∀ r3 ∈ Mv, rk r1 = rk r2 → rk r2 = rk r3 →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v)
    (hbasic : ∀ δ : Fin N → Fin b → ℝ, (∀ r v, δ r v ≠ 0 → 0 < z r v ∧ z r v < 1) →
      (∀ r, ∑ v, δ r v = 0) →
      (∀ v k, ∑ r ∈ Mv.filter (fun r => rk r = k), δ r v = 0) →
      (∀ v, ∑ r, s r * δ r v = 0) → δ = 0) :
    ∃ (y : Fin N → Fin b) (u : Fin b → ℕ → ℕ),
      (∀ r ∈ Mv, 0 < z r (y r)) ∧
      (∀ v k, ((Mv.filter fun r => rk r = k ∧ y r = v).card : ℝ) =
        ∑ r ∈ Mv.filter (fun r => rk r = k), z r v) ∧
      (∑ v, ∑ k ∈ Mv.image rk, u v k ≤ b - 1) ∧
      (∀ v k (θ : ℝ), ((Mv.filter fun r => rk r = k ∧ y r = v ∧ θ ≤ s r).card : ℝ) ≤
        ∑ r ∈ Mv.filter (fun r => rk r = k ∧ θ ≤ s r), z r v + u v k) ∧
      (∑ v, max 0 (∑ r ∈ Mv.filter (fun r => y r = v), s r - ∑ r ∈ Mv, s r * z r v) ≤
        ((∑ v, ∑ k ∈ Mv.image rk, u v k : ℕ) : ℝ) * W) := by
  have I0 : Inv s Mv rk W z z ⊥ (fun _ _ => 0) :=
    { nn := hz0
      keep := fun _ _ _ => rfl
      sup := hz1
      cnt := fun _ _ => rfl
      sw := bot_le
      sfr := by
        intro x hx hx0
        exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
      rank := by simp
      thr := by intros; simp
      ld := by intros; simp }
  obtain ⟨zf, S, u, I, hint⟩ :=
    reach s hs Mv rk W hW z hzout hzc hord _ z ⊥ _ rfl I0
  have hle1 : ∀ r v, zf r v ≤ 1 := by
    intro r v
    by_cases hr : r ∈ Mv
    · rw [← I.sup r hr]
      exact single_le_sum (fun i _ => I.nn r i) (mem_univ v)
    · have : ¬ Fr (z r v) := by simp [Fr, hzout r hr v]
      rw [I.keep r v this, hzout r hr v]; norm_num
  have h01 : ∀ r v, zf r v = 0 ∨ zf r v = 1 := by
    intro r v
    have h1 := I.nn r v
    have h2 := hle1 r v
    have h3 := hint r v
    simp only [Fr, not_and, not_lt] at h3
    rcases h1.lt_or_eq with h | h
    · right; exact le_antisymm h2 (h3 h)
    · left; exact h.symm
  let y : Fin N → Fin b := fun r => if h : ∃ v, zf r v = 1 then h.choose else ⟨0, hb⟩
  have hkey : ∀ r ∈ Mv, ∀ v, zf r v = if y r = v then 1 else 0 := by
    intro r hr v
    have hex : ∃ v, zf r v = 1 := by
      by_contra hn
      push_neg at hn
      have : ∑ v, zf r v = 0 :=
        sum_eq_zero fun v _ => (h01 r v).resolve_right (hn v)
      rw [I.sup r hr] at this; norm_num at this
    have hy : zf r (y r) = 1 := by
      simp only [y, dif_pos hex]; exact hex.choose_spec
    by_cases hv : y r = v
    · rw [if_pos hv, ← hv, hy]
    · rw [if_neg hv]
      rcases h01 r v with h | h
      · exact h
      · exfalso
        have := sum_le_sum_of_subset_of_nonneg (subset_univ {y r, v})
          (fun i _ _ => I.nn r i)
        rw [sum_pair hv, I.sup r hr, hy, h] at this
        norm_num at this
  have hcard : ∀ (p : Fin N → Prop) v,
      (((Mv.filter p).filter fun r => y r = v).card : ℝ) = ∑ r ∈ Mv.filter p, zf r v := by
    intro p v
    rw [sum_congr rfl fun r hr => hkey r (mem_filter.mp hr).1 v, sum_boole]
  refine ⟨y, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    apply I.pos r (y r)
    rw [hkey r hr]; simp
  · intro v k
    rw [← I.cnt v k]
    convert hcard (fun r => rk r = k) v using 3
    ext r; simp only [mem_filter]; tauto
  · rw [I.rank]
    exact finrank_le hb s Mv rk z hbasic S I.sw
  · intro v k θ
    refine le_of_eq_of_le ?_ (I.thr v k θ)
    convert hcard (fun r => rk r = k ∧ θ ≤ s r) v using 3
    ext r; simp only [mem_filter]; tauto
  · rw [Nat.cast_sum, sum_mul]
    apply sum_le_sum
    intro v _
    have hload : ∑ r ∈ Mv.filter (fun r => y r = v), s r = ∑ r ∈ Mv, s r * zf r v := by
      rw [sum_filter]
      refine sum_congr rfl fun r hr => ?_
      rw [hkey r hr v]; simp [eq_comm]
    rw [hload]
    by_cases hM : Mv = ∅
    · subst hM; simp
    · obtain ⟨r1, hr1⟩ := nonempty_iff_ne_empty.mpr hM
      have hWnn : 0 ≤ W := by have := hW r1 hr1 r1 hr1 rfl; simpa using this
      exact max_le (by positivity) (I.ld v)

end SublinearChoresMMS.Dev.Rearr.PartRound
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
alias round := SublinearChoresMMS.Dev.Rearr.PartRound.round

end SublinearChoresMMS.Dev.Rearr
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartFin
open SublinearChoresMMS.Dev.Rearr
/-! ## Generic rank lemmas -/
lemma card_filter_lt_strict {α : Type*} [LinearOrder α] (A : Finset α) {x x' : α}
    (hx : x ∈ A) (h : x < x') : (A.filter (· < x)).card < (A.filter (· < x')).card := by
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · exact ⟨x, by simp [hx, h], by simp⟩
  · intro y hy
    simp only [mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.trans h⟩

lemma card_filter_gt_strict {α : Type*} [LinearOrder α] (A : Finset α) {x x' : α}
    (hx' : x' ∈ A) (h : x < x') : (A.filter (x' < ·)).card < (A.filter (x < ·)).card := by
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · exact ⟨x', by simp [hx', h], by simp⟩
  · intro y hy
    simp only [mem_filter] at hy ⊢
    exact ⟨hy.1, h.trans hy.2⟩

/-- At most `n` elements have fewer than `n` predecessors. -/
lemma card_low_rank_le {α : Type*} [LinearOrder α] (A : Finset α) (n : ℕ) :
    (A.filter fun x => (A.filter (· < x)).card < n).card ≤ n := by
  calc _ ≤ (range n).card := by
        apply card_le_card_of_injOn (fun x => (A.filter (· < x)).card)
        · intro x hx
          simp only [coe_filter, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hx ⊢
          exact hx.2
        · intro x hx x' hx' heq
          simp only [coe_filter, Set.mem_ofPred_eq] at hx hx'
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := card_filter_lt_strict A hx.1 h
            simp only at heq
            omega
          · have := card_filter_lt_strict A hx'.1 h
            simp only at heq
            omega
    _ = n := card_range n

/-- At most `n` elements have fewer than `n` successors. -/
lemma card_high_rank_le {α : Type*} [LinearOrder α] (A : Finset α) (n : ℕ) :
    (A.filter fun x => (A.filter (x < ·)).card < n).card ≤ n := by
  calc _ ≤ (range n).card := by
        apply card_le_card_of_injOn (fun x => (A.filter (x < ·)).card)
        · intro x hx
          simp only [coe_filter, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hx ⊢
          exact hx.2
        · intro x hx x' hx' heq
          simp only [coe_filter, Set.mem_ofPred_eq] at hx hx'
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := card_filter_gt_strict A hx'.1 h
            simp only at heq
            omega
          · have := card_filter_gt_strict A hx.1 h
            simp only at heq
            omega
    _ = n := card_range n

/-- At least `min n |A|` elements have fewer than `n` successors. -/
lemma card_high_rank_ge {α : Type*} [LinearOrder α] (A : Finset α) (n : ℕ) :
    min n A.card ≤ (A.filter fun x => (A.filter (x < ·)).card < n).card := by
  induction A using Finset.induction_on_min with
  | empty => simp
  | insert a A ha ih =>
    have haA : a ∉ A := fun h => lt_irrefl a (ha a h)
    have hsub : (A.filter fun x => (A.filter (x < ·)).card < n) ⊆
        ((insert a A).filter fun x => ((insert a A).filter (x < ·)).card < n) := by
      intro x hx
      simp only [mem_filter] at hx
      have hxa : a < x := ha x hx.1
      have : (insert a A).filter (x < ·) = A.filter (x < ·) := by
        rw [filter_insert]; simp [not_lt.mpr hxa.le]
      simp only [mem_filter, mem_insert, this]
      exact ⟨Or.inr hx.1, hx.2⟩
    have hAa : (insert a A).filter (a < ·) = A := by
      rw [filter_insert]
      simp only [lt_self_iff_false, if_false]
      exact filter_true_of_mem ha
    rw [card_insert_of_notMem haA]
    by_cases hn : A.card < n
    · have hsub2 : insert a (A.filter fun x => (A.filter (x < ·)).card < n) ⊆
          ((insert a A).filter fun x => ((insert a A).filter (x < ·)).card < n) := by
        intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · simp [hAa, hn]
        · exact hsub hx
      have := card_le_card hsub2
      rw [card_insert_of_notMem (by simp [haA])] at this
      have h1 : min n A.card = A.card := min_eq_right hn.le
      have h2 : min n (A.card + 1) = A.card + 1 := min_eq_right hn
      omega
    · have := card_le_card hsub
      have h1 : min n A.card = n := min_eq_left (not_lt.mp hn)
      have h2 : min n (A.card + 1) = n := min_eq_left (by omega)
      omega

/-- An injection between finsets of the right sizes. -/
lemma exists_injOn_of_card_le {α : Type*} (X Y : Finset α) (h : X.card ≤ Y.card) :
    ∃ e : α → α, (∀ x ∈ X, e x ∈ Y) ∧ Set.InjOn e X := by
  have hc : Fintype.card X ≤ Fintype.card Y := by simpa using h
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun x => if hx : x ∈ X then (emb ⟨x, hx⟩ : α) else x, ?_, ?_⟩
  · intro x hx
    simp only [hx, dif_pos]
    exact (emb ⟨x, hx⟩).2
  · intro x hx x' hx' heq
    simp only [mem_coe] at hx hx'
    simp only [hx, hx', dif_pos] at heq
    have := emb.injective (Subtype.ext heq)
    simpa using this

end SublinearChoresMMS.Dev.Rearr.PartFin
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartFin
open SublinearChoresMMS.Dev.Rearr
variable {κ : ℝ} {d : ℕ}
/-! ## Range facts -/
lemma rk_bounds (hκ : 0 < κ) (hd : 1 ≤ d) {x : ℝ} (hx : 0 < x) :
    (rk κ d x : ℝ) < x * d / κ ∧ x * d / κ ≤ rk κ d x + 1 := by
  have hpos : 0 < x * d / κ := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hc : 1 ≤ ⌈x * d / κ⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hpos).ne'
  unfold rk
  have hcast : ((⌈x * d / κ⌉₊ - 1 : ℕ) : ℝ) = (⌈x * d / κ⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hc]; simp
  rw [hcast]
  constructor
  · have := Nat.lt_ceil.mp (show ⌈x * d / κ⌉₊ - 1 < ⌈x * d / κ⌉₊ by omega)
    rw [Nat.cast_sub hc] at this
    simpa using this
  · have := Nat.le_ceil (x * d / κ)
    linarith

lemma rk_lt (hκ : 0 < κ) (hd : 1 ≤ d) {x : ℝ} (_hx : 0 < x) (hxκ : x ≤ κ) : rk κ d x < d := by
  have h1 : x * d / κ ≤ d := by
    rw [div_le_iff₀ hκ]
    have : (0 : ℝ) ≤ d := by positivity
    nlinarith
  have : ⌈x * d / κ⌉₊ ≤ d := Nat.ceil_le.mpr h1
  unfold rk
  omega

lemma rk_mono (hκ : 0 < κ) {x x' : ℝ} (h : x ≤ x') : rk κ d x ≤ rk κ d x' := by
  unfold rk
  apply Nat.sub_le_sub_right
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ hκ.le
  exact mul_le_mul_of_nonneg_right h (by positivity)

lemma rk_diff (hκ : 0 < κ) (hd : 1 ≤ d) {x x' : ℝ} (hx : 0 < x) (hx' : 0 < x')
    (h : rk κ d x = rk κ d x') : x - x' < κ / d := by
  have h1 := rk_bounds hκ hd hx
  have h2 := rk_bounds hκ hd hx'
  rw [h] at h1
  have h3 : (x - x') * d / κ < 1 := by
    rw [sub_mul, sub_div]; linarith
  rw [div_lt_one hκ] at h3
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [lt_div_iff₀ hdpos]
  exact h3

end SublinearChoresMMS.Dev.Rearr.PartFin
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartFin
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
/-! ## Repacking -/
lemma repack_aux (s : Fin N → ℝ) (hs : ∀ r, 0 < s r) (cap : Fin b → ℝ) (I : Finset (Fin N)) :
    ∀ (b0 : Fin b) (rest : List (Fin b)) (c : ℝ), (b0 :: rest).Nodup → 0 ≤ c →
      (∀ v ∈ rest, 0 ≤ cap v) → ∑ r ∈ I, s r ≤ c + (rest.map cap).sum →
      ∃ R : Fin N → Option (Fin b),
        (∀ r ∈ I, ∀ v, R r = some v → v = b0 ∨ v ∈ rest) ∧
        ∑ r ∈ I.filter (fun r => R r = some b0), s r ≤ c ∧
        (∀ v ∈ rest, ∑ r ∈ I.filter (fun r => R r = some v), s r ≤ cap v) ∧
        (I.filter (fun r => R r = none)).card ≤ rest.length ∧
        (∀ r ∈ I, ∀ h : r.val + 1 < N, (⟨r.val + 1, h⟩ : Fin N) ∈ I → R r ≠ none →
          R ⟨r.val + 1, h⟩ ≠ none → R r = R ⟨r.val + 1, h⟩) ∧
        (∀ r ∈ I, (∀ r' ∈ I, r ≤ r') → R r = none ∨ R r = some b0) := by
  induction I using Finset.induction_on_min with
  | empty =>
    intro b0 rest c _ hc hcap _
    refine ⟨fun _ => none, by simp, by simpa using hc, ?_, by simp, by simp, by simp⟩
    intro v hv
    simpa using hcap v hv
  | insert a I ha ih =>
    intro b0 rest c hnd hc hcap hI
    have haI : a ∉ I := fun h => lt_irrefl a (ha a h)
    rw [sum_insert haI] at hI
    have hIpos : 0 ≤ ∑ r ∈ I, s r := sum_nonneg fun r _ => (hs r).le
    by_cases hfit : s a ≤ c
    · obtain ⟨R, h1, h2, h3, h4, h5, h6⟩ :=
        ih b0 rest (c - s a) hnd (by linarith) hcap (by linarith)
      have hRI : ∀ r ∈ I, Function.update R a (some b0) r = R r := by
        intro r hr
        rw [Function.update_of_ne]
        rintro rfl; exact haI hr
      have hfilt : ∀ (p : Option (Fin b) → Prop) [DecidablePred p],
          (insert a I).filter (fun r => p (Function.update R a (some b0) r)) =
            if p (some b0) then insert a (I.filter fun r => p (R r))
            else I.filter fun r => p (R r) := by
        intro p _
        have hc' : I.filter (fun r => p (Function.update R a (some b0) r)) =
            I.filter (fun r => p (R r)) := filter_congr (fun r hr => by rw [hRI r hr])
        rw [filter_insert, hc']
        simp only [Function.update_self]
      have hnd' := List.nodup_cons.mp hnd
      refine ⟨Function.update R a (some b0), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr v hv
        rcases mem_insert.mp hr with rfl | hr
        · simp at hv; exact Or.inl hv.symm
        · rw [hRI r hr] at hv; exact h1 r hr v hv
      · rw [hfilt (fun o => o = some b0)]
        simp only [if_true]
        rw [sum_insert (by simp [haI])]
        linarith
      · intro v hv
        have hvb : v ≠ b0 := fun h => hnd'.1 (h ▸ hv)
        rw [hfilt (fun o => o = some v)]
        simp only [Option.some.injEq, hvb.symm, if_false]
        exact h3 v hv
      · rw [hfilt (fun o => o = none)]
        simp only [reduceCtorEq, if_false]
        exact h4
      · intro r hr h hr1 hn1 hn2
        rcases mem_insert.mp hr with rfl | hr
        · have hr1' : (⟨r.val + 1, h⟩ : Fin N) ∈ I := by
            rcases mem_insert.mp hr1 with h' | h'
            · exact absurd (congrArg Fin.val h') (by simp)
            · exact h'
          have hmin : ∀ r' ∈ I, (⟨r.val + 1, h⟩ : Fin N) ≤ r' := by
            intro r' hr'
            have := ha r' hr'
            rw [Fin.le_def]; rw [Fin.lt_def] at this; simp; omega
          rw [hRI _ hr1'] at hn2 ⊢
          rcases h6 _ hr1' hmin with h7 | h7
          · exact absurd h7 hn2
          · rw [h7]; simp
        · have hr1' : (⟨r.val + 1, h⟩ : Fin N) ∈ I := by
            rcases mem_insert.mp hr1 with h' | h'
            · have := ha r hr
              rw [Fin.lt_def] at this
              have := congrArg Fin.val h'
              simp at this; omega
            · exact h'
          rw [hRI _ hr1'] at hn2 ⊢; rw [hRI _ hr] at hn1 ⊢
          exact h5 r hr h hr1' hn1 hn2
      · intro r hr hmin
        rcases mem_insert.mp hr with rfl | hr
        · simp
        · exact absurd (hmin a (mem_insert_self _ _)) (not_le.mpr (ha r hr))
    · push Not at hfit
      cases rest with
      | nil =>
        simp at hI; linarith
      | cons b1 rest' =>
        have hnd' := List.nodup_cons.mp hnd
        have hnd1 := List.nodup_cons.mp hnd'.2
        simp only [List.map_cons, List.sum_cons] at hI
        obtain ⟨R, h1, h2, h3, h4, h5, h6⟩ :=
          ih b1 rest' (cap b1) hnd'.2 (hcap b1 (by simp))
            (fun v hv => hcap v (by simp [hv])) (by linarith)
        have hRI : ∀ r ∈ I, Function.update R a none r = R r := by
          intro r hr
          rw [Function.update_of_ne]
          rintro rfl; exact haI hr
        have hfilt : ∀ (p : Option (Fin b) → Prop) [DecidablePred p],
            (insert a I).filter (fun r => p (Function.update R a none r)) =
              if p none then insert a (I.filter fun r => p (R r))
              else I.filter fun r => p (R r) := by
          intro p _
          have hc' : I.filter (fun r => p (Function.update R a none r)) =
              I.filter (fun r => p (R r)) := filter_congr (fun r hr => by rw [hRI r hr])
          rw [filter_insert, hc']
          simp only [Function.update_self]
        refine ⟨Function.update R a none, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro r hr v hv
          rcases mem_insert.mp hr with rfl | hr
          · simp at hv
          · rw [hRI r hr] at hv
            rcases h1 r hr v hv with h | h
            · right; simp [h]
            · right; simp [h]
        · rw [hfilt (fun o => o = some b0)]
          simp only [reduceCtorEq, if_false]
          have : I.filter (fun r => R r = some b0) = ∅ := by
            rw [filter_eq_empty_iff]
            intro r hr hR
            rcases h1 r hr b0 hR with h | h
            · exact hnd'.1 (by simp [h])
            · exact hnd'.1 (by simp [h])
          rw [this, sum_empty]; exact hc
        · intro v hv
          rw [hfilt (fun o => o = some v)]
          simp only [reduceCtorEq, if_false]
          rcases List.mem_cons.mp hv with rfl | hv
          · exact h2
          · exact h3 v hv
        · rw [hfilt (fun o => o = none)]
          simp only [if_true]
          rw [card_insert_of_notMem (by simp [haI])]
          simp only [List.length_cons]
          omega
        · intro r hr h hr1 hn1 hn2
          rcases mem_insert.mp hr with rfl | hr
          · simp at hn1
          · have hr1' : (⟨r.val + 1, h⟩ : Fin N) ∈ I := by
              rcases mem_insert.mp hr1 with h' | h'
              · have := ha r hr
                rw [Fin.lt_def] at this
                have := congrArg Fin.val h'
                simp at this; omega
              · exact h'
            rw [hRI _ hr1'] at hn2 ⊢; rw [hRI _ hr] at hn1 ⊢
            exact h5 r hr h hr1' hn1 hn2
        · intro r hr hmin
          rcases mem_insert.mp hr with rfl | hr
          · simp
          · exact absurd (hmin a (mem_insert_self _ _)) (not_le.mpr (ha r hr))

/-- Repack items `I` into the bins of a list, in index order: all bins valid, at most
`L.length` exclusions, consecutive packed items in the same bin. -/
lemma repack (s : Fin N → ℝ) (hs : ∀ r, 0 < s r) (cap : Fin b → ℝ) (L : List (Fin b))
    (hL : L.Nodup) (hcap : ∀ v ∈ L, 0 ≤ cap v) (I : Finset (Fin N))
    (hI : ∑ r ∈ I, s r ≤ (L.map cap).sum) :
    ∃ R : Fin N → Option (Fin b),
      (∀ r ∈ I, ∀ v, R r = some v → v ∈ L) ∧
      (∀ v ∈ L, ∑ r ∈ I.filter (fun r => R r = some v), s r ≤ cap v) ∧
      (I.filter (fun r => R r = none)).card ≤ L.length ∧
      (∀ r ∈ I, ∀ h : r.val + 1 < N, (⟨r.val + 1, h⟩ : Fin N) ∈ I → R r ≠ none →
        R ⟨r.val + 1, h⟩ ≠ none → R r = R ⟨r.val + 1, h⟩) := by
  cases L with
  | nil =>
    have hIe : I = ∅ := by
      by_contra hne
      have := sum_pos (fun r _ => hs r) (nonempty_iff_ne_empty.mpr hne)
      simp at hI; linarith
    subst hIe
    exact ⟨fun _ => none, by simp, by simp, by simp, by simp⟩
  | cons b0 rest =>
    simp only [List.map_cons, List.sum_cons] at hI
    obtain ⟨R, h1, h2, h3, h4, h5, -⟩ := repack_aux s hs cap I b0 rest (cap b0) hL
      (hcap b0 (by simp)) (fun v hv => hcap v (by simp [hv])) hI
    refine ⟨R, ?_, ?_, ?_, h5⟩
    · intro r hr v hv
      rcases h1 r hr v hv with h | h
      · simp [h]
      · simp [h]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact h2
      · exact h3 v hv
    · simp only [List.length_cons]; omega

end SublinearChoresMMS.Dev.Rearr.PartFin
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartFin
open SublinearChoresMMS.Dev.Rearr
/-! ## Threshold lemma -/
lemma step_integral (m0 K x : ℝ) (h1 : m0 ≤ x) (h2 : x ≤ K) :
    ∫ θ in m0..K, (if θ ≤ x then (1 : ℝ) else 0) = x - m0 := by
  have hanti : Antitone (fun θ : ℝ => if θ ≤ x then (1 : ℝ) else 0) := by
    intro a c hac
    simp only
    split_ifs <;> (try push Not at *) <;> linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hanti.intervalIntegrable)
    (hanti.intervalIntegrable)]
  have e1 : ∫ θ in m0..x, (if θ ≤ x then (1 : ℝ) else 0) = ∫ θ in m0..x, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le h1] at hθ
    simp [hθ.2]
  have e2 : ∫ θ in x..K, (if θ ≤ x then (1 : ℝ) else 0) = ∫ θ in x..K, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun θ hθ => ?_)
    rw [Set.uIoc_of_le h2] at hθ
    simp [not_le.mpr hθ.1]
  rw [e1, e2]
  simp

lemma layer_cake_le {ι : Type*} (X Mk : Finset ι) (sz zz : ι → ℝ) (m0 : ℝ)
    (hz : ∀ r ∈ Mk, 0 ≤ zz r) (hX : ∀ x ∈ X, m0 ≤ sz x) (hM : ∀ r ∈ Mk, m0 ≤ sz r)
    (h : ∀ θ, ((X.filter fun x => θ ≤ sz x).card : ℝ) ≤
      ∑ r ∈ Mk.filter (fun r => θ ≤ sz r), zz r) :
    ∑ x ∈ X, (sz x - m0) ≤ ∑ r ∈ Mk, (sz r - m0) * zz r := by
  set K := m0 + ∑ x ∈ X, |sz x - m0| + ∑ r ∈ Mk, |sz r - m0| with hK
  have hS1 : 0 ≤ ∑ x ∈ X, |sz x - m0| := sum_nonneg (fun _ _ => abs_nonneg _)
  have hS2 : 0 ≤ ∑ r ∈ Mk, |sz r - m0| := sum_nonneg (fun _ _ => abs_nonneg _)
  have hKX : ∀ x ∈ X, sz x ≤ K := by
    intro x hx
    have h1 := single_le_sum (f := fun x => |sz x - m0|) (fun _ _ => abs_nonneg _) hx
    have h2 := le_abs_self (sz x - m0)
    linarith
  have hKM : ∀ r ∈ Mk, sz r ≤ K := by
    intro r hr
    have h1 := single_le_sum (f := fun r => |sz r - m0|) (fun _ _ => abs_nonneg _) hr
    have h2 := le_abs_self (sz r - m0)
    linarith
  have hm0K : m0 ≤ K := by linarith
  have hanti : ∀ t : ℝ, Antitone (fun θ : ℝ => if θ ≤ t then (1 : ℝ) else 0) := by
    intro t a c hac
    simp only
    split_ifs <;> (try push Not at *) <;> linarith
  have hL : ∑ x ∈ X, (sz x - m0) =
      ∫ θ in m0..K, ∑ x ∈ X, (if θ ≤ sz x then (1 : ℝ) else 0) := by
    rw [intervalIntegral.integral_finsetSum (fun x _ => (hanti _).intervalIntegrable)]
    apply sum_congr rfl
    intro x hx
    rw [step_integral m0 K _ (hX x hx) (hKX x hx)]
  have hR : ∑ r ∈ Mk, (sz r - m0) * zz r =
      ∫ θ in m0..K, ∑ r ∈ Mk, (if θ ≤ sz r then (1 : ℝ) else 0) * zz r := by
    rw [intervalIntegral.integral_finsetSum
      (fun r _ => ((hanti _).intervalIntegrable).mul_const _)]
    apply sum_congr rfl
    intro r hr
    rw [intervalIntegral.integral_mul_const, step_integral m0 K _ (hM r hr) (hKM r hr)]
  rw [hL, hR]
  have hf : Antitone (fun θ : ℝ => ∑ x ∈ X, (if θ ≤ sz x then (1 : ℝ) else 0)) :=
    fun a c hac => sum_le_sum (fun x _ => hanti _ hac)
  have hg : Antitone (fun θ : ℝ => ∑ r ∈ Mk, (if θ ≤ sz r then (1 : ℝ) else 0) * zz r) :=
    fun a c hac => sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right (hanti _ hac) (hz r hr))
  apply intervalIntegral.integral_mono_on hm0K hf.intervalIntegrable hg.intervalIntegrable
  intro θ _
  have e1 : ∑ x ∈ X, (if θ ≤ sz x then (1 : ℝ) else 0) =
      ((X.filter fun x => θ ≤ sz x).card : ℝ) := by
    rw [sum_boole]
  have e2 : ∑ r ∈ Mk, (if θ ≤ sz r then (1 : ℝ) else 0) * zz r =
      ∑ r ∈ Mk.filter (fun r => θ ≤ sz r), zz r := by
    rw [sum_filter]
    apply sum_congr rfl
    intro r _
    split_ifs <;> simp
  rw [e1, e2]
  exact h θ

/-- The threshold lemma: kept items dominated in the threshold order by a fractional
distribution, plus received items below every size of the distribution, weigh at most the
distribution's load. -/
lemma threshold {ι : Type*} [DecidableEq ι] (A Out Mk : Finset ι) (sz zz gs : ι → ℝ)
    (hOut : Out ⊆ A) (hA : A ⊆ Mk) (hz : ∀ r ∈ Mk, 0 ≤ zz r)
    (hgs : ∀ x ∈ Out, ∀ r ∈ Mk, gs x ≤ sz r)
    (hcard : (A.card : ℝ) = ∑ r ∈ Mk, zz r)
    (hcnt : ∀ θ, (((A \ Out).filter fun x => θ ≤ sz x).card : ℝ) ≤
      ∑ r ∈ Mk.filter (fun r => θ ≤ sz r), zz r) :
    ∑ x ∈ A \ Out, sz x + ∑ x ∈ Out, gs x ≤ ∑ r ∈ Mk, sz r * zz r := by
  rcases Mk.eq_empty_or_nonempty with hMk | hne
  · subst hMk
    have : A = ∅ := subset_empty.mp hA
    subst this
    have : Out = ∅ := subset_empty.mp hOut
    subst this
    simp
  set m0 := Mk.inf' hne sz
  have hM : ∀ r ∈ Mk, m0 ≤ sz r := fun r hr => inf'_le _ hr
  have hX : ∀ x ∈ A \ Out, m0 ≤ sz x := fun x hx => hM x (hA (mem_sdiff.mp hx).1)
  have hg : ∀ x ∈ Out, gs x ≤ m0 := fun x hx => le_inf' _ _ (hgs x hx)
  have key := layer_cake_le (A \ Out) Mk sz zz m0 hz hX hM hcnt
  have hcardsd : ((A \ Out).card : ℝ) + Out.card = A.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hOut
  have e1 : ∑ x ∈ A \ Out, (sz x - m0) = ∑ x ∈ A \ Out, sz x - (A \ Out).card * m0 := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have e2 : ∑ r ∈ Mk, (sz r - m0) * zz r = ∑ r ∈ Mk, sz r * zz r - m0 * ∑ r ∈ Mk, zz r := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    ring
  have e3 : ∑ x ∈ Out, gs x ≤ Out.card * m0 := by
    calc _ ≤ ∑ x ∈ Out, m0 := sum_le_sum hg
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  rw [e1, e2, ← hcard, ← hcardsd] at key
  nlinarith

end SublinearChoresMMS.Dev.Rearr.PartFin
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartFin
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
/-! ## Label changes along one sequence -/
/-- The successor index (or `r` itself at the end). -/
def nx (r : Fin N) : Fin N := if h : r.val + 1 < N then ⟨r.val + 1, h⟩ else r

lemma nx_eq (r : Fin N) (h : r.val + 1 < N) : nx r = ⟨r.val + 1, h⟩ := by
  simp [nx, h]

lemma ychanges_le (M : Finset (Fin N)) (f : Fin N → ℕ) (d : ℕ) (y : Fin N → Fin b)
    (hfanti : ∀ r ∈ M, ∀ r' ∈ M, r ≤ r' → f r' ≤ f r)
    (hfd : ∀ r ∈ M, f r < d)
    (huvuv : ∀ r1 ∈ M, ∀ r2 ∈ M, ∀ r3 ∈ M, ∀ r4 ∈ M, r1 < r2 → r2 < r3 → r3 < r4 →
      f r1 = f r4 → y r1 = y r3 → y r2 = y r4 → y r1 ≠ y r2 → False) :
    (univ.filter fun r : Fin N => ∃ h : r.val + 1 < N, r ∈ M ∧ (⟨r.val + 1, h⟩ : Fin N) ∈ M ∧
      y r ≠ y ⟨r.val + 1, h⟩).card ≤ d + d * (b * b) := by
  set C := univ.filter fun r : Fin N => ∃ h : r.val + 1 < N, r ∈ M ∧
    (⟨r.val + 1, h⟩ : Fin N) ∈ M ∧ y r ≠ y ⟨r.val + 1, h⟩ with hC
  have hCmem : ∀ r ∈ C, r.val + 1 < N ∧ r ∈ M ∧ nx r ∈ M ∧ y r ≠ y (nx r) := by
    intro r hr
    simp only [hC, mem_filter, mem_univ, true_and] at hr
    obtain ⟨h, h1, h2, h3⟩ := hr
    rw [nx_eq r h]
    exact ⟨h, h1, h2, h3⟩
  have hlt : ∀ r : Fin N, r.val + 1 < N → r < nx r := by
    intro r h; rw [nx_eq r h, Fin.lt_def]; simp
  have hle : ∀ r r' : Fin N, r.val + 1 < N → r < r' → nx r ≤ r' := by
    intro r r' h h'; rw [nx_eq r h, Fin.le_def]; rw [Fin.lt_def] at h'; simp; omega
  rw [← card_filter_add_card_filter_not (fun r => f r = f (nx r)), add_comm d]
  apply add_le_add
  · -- same range
    calc _ ≤ (range d ×ˢ (univ : Finset (Fin b)) ×ˢ (univ : Finset (Fin b))).card := by
          apply card_le_card_of_injOn (fun r => (f r, y r, y (nx r)))
          · intro r hr
            simp only [coe_filter, Set.mem_ofPred_eq] at hr
            have := hCmem r hr.1
            simp only [coe_product, coe_range, coe_univ, Set.mem_prod, Set.mem_Iio,
              Set.mem_univ, and_true]
            exact hfd r this.2.1
          · intro r hr r' hr' heq
            simp only [coe_filter, Set.mem_ofPred_eq] at hr hr'
            simp only [Prod.mk.injEq] at heq
            obtain ⟨hf, hy1, hy2⟩ := heq
            have h1 := hCmem r hr.1
            have h2 := hCmem r' hr'.1
            by_contra hne
            rcases lt_or_gt_of_ne hne with h | h
            · have hn : nx r ≠ r' := by
                intro he; apply h1.2.2.2; rw [hy1, he]
              have h3 := lt_of_le_of_ne (hle r r' h1.1 h) hn
              exact huvuv r h1.2.1 (nx r) h1.2.2.1 r' h2.2.1 (nx r') h2.2.2.1 (hlt r h1.1) h3
                (hlt r' h2.1) (by rw [hf, hr'.2]) hy1 hy2 h1.2.2.2
            · have hn : nx r' ≠ r := by
                intro he; apply h2.2.2.2; rw [← hy1, he]
              have h3 := lt_of_le_of_ne (hle r' r h2.1 h) hn
              exact huvuv r' h2.2.1 (nx r') h2.2.2.1 r h1.2.1 (nx r) h1.2.2.1 (hlt r' h2.1) h3
                (hlt r h1.1) (by rw [← hf, hr.2]) hy1.symm hy2.symm h2.2.2.2
      _ = d * (b * b) := by simp
  · -- range changes
    calc _ ≤ (range d).card := by
          apply card_le_card_of_injOn (fun r => f (nx r))
          · intro r hr
            simp only [coe_filter, Set.mem_ofPred_eq] at hr
            have := hCmem r hr.1
            simp only [coe_range, Set.mem_Iio]
            exact hfd _ this.2.2.1
          · intro r hr r' hr' heq
            simp only [coe_filter, Set.mem_ofPred_eq] at hr hr'
            simp only at heq
            have h1 := hCmem r hr.1
            have h2 := hCmem r' hr'.1
            by_contra hne
            rcases lt_or_gt_of_ne hne with h | h
            · have a1 := hfanti _ h1.2.2.1 _ h2.2.1 (hle r r' h1.1 h)
              have a2 := hfanti _ h2.2.1 _ h2.2.2.1 (hlt r' h2.1).le
              have : f (nx r') ≠ f r' := fun e => hr'.2 e.symm
              omega
            · have a1 := hfanti _ h2.2.2.1 _ h1.2.1 (hle r' r h2.1 h)
              have a2 := hfanti _ h1.2.1 _ h1.2.2.1 (hlt r h1.1).le
              have : f (nx r) ≠ f r := fun e => hr.2 e.symm
              omega
      _ = d := card_range d

end SublinearChoresMMS.Dev.Rearr.PartFin
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartFin
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ} (s : Fin N → ℝ) (κ : ℝ) (d : ℕ) (P1 : Asg N b)
/-! ## Fixed and movable items -/
/-- Non-excluded items of range `k`. -/
def Zr (k : ℕ) : Finset (Fin N) := univ.filter fun r => P1 r ≠ none ∧ rk κ d (s r) = k

lemma mem_Zr (k : ℕ) (r : Fin N) :
    r ∈ Zr s κ d P1 k ↔ P1 r ≠ none ∧ rk κ d (s r) = k := by
  simp [Zr]

lemma above_eq (r : Fin N) :
    (univ.filter fun r' => r < r' ∧ P1 r' ≠ none ∧ rk κ d (s r') = rk κ d (s r)) =
      (Zr s κ d P1 (rk κ d (s r))).filter (r < ·) := by
  ext r'
  simp only [Zr, mem_filter, mem_univ, true_and]
  tauto

lemma isFixed_iff (r : Fin N) : IsFixed s κ d P1 r ↔
    P1 r ≠ none ∧ ((Zr s κ d P1 (rk κ d (s r))).filter (r < ·)).card < b * (b - 1) := by
  unfold IsFixed
  rw [above_eq]

lemma fixed_filter_eq (k : ℕ) :
    (univ.filter fun r => IsFixed s κ d P1 r ∧ rk κ d (s r) = k) =
      (Zr s κ d P1 k).filter fun x => ((Zr s κ d P1 k).filter (x < ·)).card < b * (b - 1) := by
  ext r
  simp only [mem_filter, mem_univ, true_and, isFixed_iff, mem_Zr]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    subst h3
    exact ⟨⟨h1, rfl⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    subst h3
    exact ⟨⟨h1, h2⟩, rfl⟩

lemma card_fixed_range_le (k : ℕ) :
    (univ.filter fun r => IsFixed s κ d P1 r ∧ rk κ d (s r) = k).card ≤ b * (b - 1) := by
  rw [fixed_filter_eq]
  exact card_high_rank_le _ _

lemma movable_mem (r : Fin N) :
    r ∈ movable s κ d P1 ↔ P1 r ≠ none ∧ ¬ IsFixed s κ d P1 r := by
  simp [movable]

lemma card_fixed_range_ge (m : Fin N) (hm : m ∈ movable s κ d P1) (k : ℕ)
    (hk : rk κ d (s m) = k) :
    b * (b - 1) ≤ (univ.filter fun r => IsFixed s κ d P1 r ∧ rk κ d (s r) = k).card := by
  rw [fixed_filter_eq]
  refine le_trans ?_ (card_high_rank_ge _ _)
  rw [movable_mem, isFixed_iff] at hm
  push Not at hm
  have hmZ : m ∈ Zr s κ d P1 k := by simp [Zr, hm.1, hk]
  have h1 := hm.2 hm.1
  rw [hk] at h1
  have h2 : ((Zr s κ d P1 k).filter (m < ·)).card < (Zr s κ d P1 k).card := by
    apply card_lt_card
    rw [ssubset_iff_of_subset (filter_subset _ _)]
    exact ⟨m, hmZ, by simp⟩
  omega

lemma fixed_lt_movable (f m : Fin N) (hf : IsFixed s κ d P1 f) (hm : m ∈ movable s κ d P1)
    (hk : rk κ d (s f) = rk κ d (s m)) : m < f := by
  rw [movable_mem] at hm
  by_contra hlt
  push Not at hlt
  rcases lt_or_eq_of_le hlt with h | h
  · rw [isFixed_iff] at hf
    have h1 := hm.2
    rw [isFixed_iff] at h1
    push Not at h1
    have h2 := h1 hm.1
    have hmZ : m ∈ Zr s κ d P1 (rk κ d (s f)) := by simp [Zr, hm.1, hk]
    have h3 := card_filter_gt_strict (Zr s κ d P1 (rk κ d (s f))) hmZ h
    rw [hk] at h3 hf
    omega
  · subst h
    exact hm.2 hf

end SublinearChoresMMS.Dev.Rearr.PartFin
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartFin
open SublinearChoresMMS.Dev.Rearr
/-! ## Sum helpers -/
lemma sum_filter_univ {N : ℕ} (S : Finset (Fin N)) (p : Fin N → Prop) [DecidablePred p]
    (f : Fin N → ℝ) : ∑ r ∈ S.filter p, f r = ∑ r, if r ∈ S ∧ p r then f r else 0 := by
  rw [← sum_filter]
  congr 1
  ext r
  simp

lemma sum_mem_univ {N : ℕ} (S : Finset (Fin N)) (f : Fin N → ℝ) :
    ∑ r ∈ S, f r = ∑ r, if r ∈ S then f r else 0 := by
  rw [← sum_filter]
  congr 1
  ext r
  simp

lemma sum_ite_and_eq {α : Type*} [DecidableEq α] (S : Finset α) (a : α) (p : Prop) [Decidable p]
    (c : ℝ) : ∑ v ∈ S, (if p ∧ a = v then c else 0) = if p ∧ a ∈ S then c else 0 := by
  by_cases hp : p <;> simp [hp]

lemma sum_ite_and_some {b : ℕ} (S : Finset (Fin b)) (o : Option (Fin b)) (p : Prop)
    [Decidable p] (c : ℝ) :
    ∑ v ∈ S, (if p ∧ o = some v then c else 0) = if p ∧ ∃ w ∈ S, o = some w then c else 0 := by
  cases o with
  | none => simp
  | some w =>
    simp only [Option.some.injEq]
    rw [sum_ite_and_eq]
    congr 1
    apply propext
    constructor
    · rintro ⟨hp, hw⟩; exact ⟨hp, w, hw, rfl⟩
    · rintro ⟨hp, w', hw', rfl⟩; exact ⟨hp, hw'⟩

/-! ## Steps 4–5 -/
theorem finish (N b d : ℕ) (hd : 1 ≤ d) (hbd : b ≤ d ^ 2) (s : Fin N → ℝ) (hs : StrictAnti s)
    (hpos : ∀ r, 0 < s r) (T : Fin b → ℝ) (P1 : Asg N b) (hP1 : ∀ v, load s P1 v ≤ T v)
    (κ : ℝ) (hκ : 0 < κ) (V : Finset (Fin b)) (hV : V.card ≤ 2 * d)
    (hsmall : ∀ r, P1 r ≠ none → s r ≤ κ)
    (hslack : 2 * d * κ ≤ ∑ v ∈ V, (T v - load s P1 v))
    (z : Fin N → Fin b → ℝ) (y : Fin N → Fin b) (u : Fin b → ℕ → ℕ)
    (hzout : ∀ r ∉ movable s κ d P1, ∀ v, z r v = 0)
    (hzload : ∀ v, ∑ r ∈ movable s κ d P1, s r * z r v =
      ∑ r ∈ (movable s κ d P1).filter (fun r => P1 r = some v), s r)
    (hzc : ∀ v k, ∑ r ∈ (movable s κ d P1).filter (fun r => rk κ d (s r) = k), z r v =
      (((movable s κ d P1).filter fun r => rk κ d (s r) = k ∧ P1 r = some v).card : ℝ))
    (hz0 : ∀ r v, 0 ≤ z r v)
    (hord : ∀ u v : Fin b, ∀ r1 ∈ movable s κ d P1, ∀ r2 ∈ movable s κ d P1,
      ∀ r3 ∈ movable s κ d P1, rk κ d (s r1) = rk κ d (s r2) → rk κ d (s r2) = rk κ d (s r3) →
      s r1 < s r2 → s r2 < s r3 → 0 < z r1 u → 0 < z r2 v → 0 < z r3 u → u ≠ v → u < v)
    (hy1 : ∀ r ∈ movable s κ d P1, 0 < z r (y r))
    (hy2 : ∀ v k, (((movable s κ d P1).filter fun r => rk κ d (s r) = k ∧ y r = v).card : ℝ) =
      ∑ r ∈ (movable s κ d P1).filter (fun r => rk κ d (s r) = k), z r v)
    (hu : ∑ v, ∑ k ∈ (movable s κ d P1).image (fun r => rk κ d (s r)), u v k ≤ b - 1)
    (hy4 : ∀ v k (θ : ℝ), (((movable s κ d P1).filter
        fun r => rk κ d (s r) = k ∧ y r = v ∧ θ ≤ s r).card : ℝ) ≤
      ∑ r ∈ (movable s κ d P1).filter (fun r => rk κ d (s r) = k ∧ θ ≤ s r), z r v + u v k)
    (hy5 : ∑ v, max 0 (∑ r ∈ (movable s κ d P1).filter (fun r => y r = v), s r -
        ∑ r ∈ movable s κ d P1, s r * z r v) ≤
      ((∑ v, ∑ k ∈ (movable s κ d P1).image (fun r => rk κ d (s r)), u v k : ℕ) : ℝ) * (κ / d)) :
    ∃ P' : Asg N b, (∀ v, load s P' v ≤ T v) ∧ excl P' ≤ excl P1 + 3 * d ∧
      changes P' ≤ 2 * excl P1 + 20 * d * (b + 1) ^ 2 := by
  -- the trivial case without bins
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    have hall : ∀ r, P1 r = none := by
      intro r
      cases h : P1 r with
      | none => rfl
      | some v => exact v.elim0
    refine ⟨P1, hP1, by omega, ?_⟩
    have : changes P1 = 0 := by
      unfold changes
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro r - ⟨h, hne⟩
      exact hne (by rw [hall, hall])
    omega
  have v0 : Fin b := ⟨0, hbpos⟩
  set M := movable s κ d P1 with hMdef
  have hMmem : ∀ r, r ∈ M ↔ P1 r ≠ none ∧ ¬ IsFixed s κ d P1 r :=
    fun r => movable_mem s κ d P1 r
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hrkd : ∀ r, P1 r ≠ none → rk κ d (s r) < d :=
    fun r h => rk_lt hκ hd (hpos r) (hsmall r h)
  have hrkanti : ∀ r r' : Fin N, r ≤ r' → rk κ d (s r') ≤ rk κ d (s r) :=
    fun r r' h => rk_mono hκ (hs.antitone h)
  have hsame : ∀ r r' : Fin N, rk κ d (s r) = rk κ d (s r') → s r - s r' < κ / d :=
    fun r r' h => rk_diff hκ hd (hpos r) (hpos r') h
  have hMrk : ∀ r ∈ M, rk κ d (s r) < d := fun r hr => hrkd r ((hMmem r).mp hr).1
  ------------------------------------------------------------------
  -- the bins `v_k`
  ------------------------------------------------------------------
  set Fix : Fin b → ℕ → Finset (Fin N) := fun v k =>
    univ.filter (fun r => IsFixed s κ d P1 r ∧ rk κ d (s r) = k ∧ P1 r = some v) with hFix
  have hvk_ex : ∀ k, ∃ v, ∀ w, (Fix w k).card ≤ (Fix v k).card := by
    intro k
    obtain ⟨v, -, hv⟩ := exists_max_image univ (fun w => (Fix w k).card) ⟨v0, mem_univ _⟩
    exact ⟨v, fun w => hv w (mem_univ _)⟩
  choose vk hvk using hvk_ex
  have hvk_big : ∀ m ∈ M, b - 1 ≤ (Fix (vk (rk κ d (s m))) (rk κ d (s m))).card := by
    intro m hm
    have h1 := card_fixed_range_ge s κ d P1 m hm _ rfl
    have h2 : (univ.filter fun r => IsFixed s κ d P1 r ∧ rk κ d (s r) = rk κ d (s m)).card =
        ∑ w, (Fix w (rk κ d (s m))).card := by
      rw [card_eq_sum_card_fiberwise (f := fun r => (P1 r).getD v0) (t := univ)
        (fun _ _ => mem_univ _)]
      apply sum_congr rfl
      intro w _
      congr 1
      ext r
      simp only [hFix, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hf, hk⟩, hw⟩
        refine ⟨hf, hk, ?_⟩
        cases h : P1 r with
        | none => exact absurd h hf.1
        | some w' => rw [h] at hw; simp at hw; rw [hw]
      · rintro ⟨hf, hk, hw⟩
        exact ⟨⟨hf, hk⟩, by rw [hw]; simp⟩
    have h3 : ∑ w, (Fix w (rk κ d (s m))).card ≤ b * (Fix (vk (rk κ d (s m))) (rk κ d (s m))).card := by
      calc _ ≤ ∑ w : Fin b, (Fix (vk (rk κ d (s m))) (rk κ d (s m))).card :=
            sum_le_sum (fun w _ => hvk _ w)
        _ = _ := by simp
    have : b * (b - 1) ≤ b * (Fix (vk (rk κ d (s m))) (rk κ d (s m))).card := by omega
    exact Nat.le_of_mul_le_mul_left this hbpos
  set K := M.image (fun r => rk κ d (s r)) with hK
  have hKd : K ⊆ range d := by
    intro k hk
    rw [hK, mem_image] at hk
    obtain ⟨r, hr, rfl⟩ := hk
    rw [mem_range]
    exact hMrk r hr
  obtain ⟨V', hV'card, hVV', hvkV'⟩ : ∃ V' : Finset (Fin b), V'.card ≤ 3 * d ∧ V ⊆ V' ∧
      ∀ m ∈ M, vk (rk κ d (s m)) ∈ V' := by
    refine ⟨V ∪ K.image vk, ?_, subset_union_left, ?_⟩
    · have h1 := card_union_le V (K.image vk)
      have h2 := card_image_le (s := K) (f := vk)
      have h3 := card_le_card hKd
      rw [card_range] at h3
      omega
    · intro m hm
      apply mem_union_right
      exact mem_image_of_mem _ (mem_image_of_mem _ hm)
  ------------------------------------------------------------------
  -- the swapped movable items
  ------------------------------------------------------------------
  obtain ⟨A, hAeq⟩ : ∃ A : Fin b → ℕ → Finset (Fin N), ∀ v k,
      A v k = M.filter (fun r => rk κ d (s r) = k ∧ y r = v) := ⟨_, fun _ _ => rfl⟩
  have hAmem : ∀ v k r, r ∈ A v k ↔ r ∈ M ∧ rk κ d (s r) = k ∧ y r = v := by
    intro v k r; rw [hAeq, mem_filter]
  obtain ⟨SwM, hSwmem⟩ : ∃ S : Finset (Fin N), ∀ r, r ∈ S ↔ r ∈ M ∧ y r ∉ V' ∧
      ((A (y r) (rk κ d (s r))).filter (· < r)).card < u (y r) (rk κ d (s r)) :=
    ⟨M.filter _, fun r => mem_filter⟩
  have hSwM_M : SwM ⊆ M := fun r hr => ((hSwmem r).mp hr).1
  have hSwvk : ∀ v k, (SwM.filter (fun r => rk κ d (s r) = k ∧ y r = v)).card ≤ u v k := by
    intro v k
    refine le_trans (card_le_card ?_) (card_low_rank_le (A v k) (u v k))
    intro r hr
    rw [mem_filter] at hr
    obtain ⟨hr1, hk, hv⟩ := hr
    rw [hSwmem] at hr1
    rw [mem_filter, hAmem]
    subst hk hv
    exact ⟨⟨hr1.1, rfl, rfl⟩, hr1.2.2⟩
  have hsumu : ∀ k ∈ K, ∑ v, u v k ≤ b - 1 := by
    intro k hk
    calc ∑ v, u v k ≤ ∑ v, ∑ k' ∈ K, u v k' :=
          sum_le_sum (fun v _ => single_le_sum (f := fun k' => u v k')
            (fun _ _ => Nat.zero_le _) hk)
      _ ≤ b - 1 := hu
  have hSwk : ∀ k, (SwM.filter (fun r => rk κ d (s r) = k)).card ≤ ∑ v, u v k := by
    intro k
    rw [card_eq_sum_card_fiberwise (f := y) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_le_sum
    intro v _
    rw [filter_filter]
    exact hSwvk v k
  have hSwcard : SwM.card ≤ b - 1 := by
    rw [card_eq_sum_card_fiberwise (f := fun r => rk κ d (s r)) (t := K)
      (fun r hr => mem_image_of_mem _ (hSwM_M hr))]
    calc ∑ k ∈ K, (SwM.filter (fun r => rk κ d (s r) = k)).card ≤ ∑ k ∈ K, ∑ v, u v k :=
          sum_le_sum (fun k _ => hSwk k)
      _ = ∑ v, ∑ k ∈ K, u v k := sum_comm
      _ ≤ b - 1 := hu
  have hSwFix : ∀ k, (SwM.filter (fun r => rk κ d (s r) = k)).card ≤ (Fix (vk k) k).card := by
    intro k
    rcases (SwM.filter (fun r => rk κ d (s r) = k)).eq_empty_or_nonempty with he | ⟨m, hm⟩
    · rw [he]; simp
    · rw [mem_filter] at hm
      have hmM := hSwM_M hm.1
      have hkK : k ∈ K := by rw [← hm.2]; exact mem_image_of_mem _ hmM
      have := hvk_big m hmM
      rw [hm.2] at this
      exact le_trans (hSwk k) (le_trans (hsumu k hkK) this)
  choose e he using fun k => exists_injOn_of_card_le
    (SwM.filter (fun r => rk κ d (s r) = k)) (Fix (vk k) k) (hSwFix k)
  obtain ⟨g, hgfix, hginj⟩ : ∃ g : Fin N → Fin N, (∀ r ∈ SwM, IsFixed s κ d P1 (g r) ∧
      rk κ d (s (g r)) = rk κ d (s r) ∧ P1 (g r) = some (vk (rk κ d (s r)))) ∧
      Set.InjOn g SwM := by
    refine ⟨fun r => e (rk κ d (s r)) r, ?_, ?_⟩
    · intro r hr
      have := (he (rk κ d (s r))).1 r (by rw [mem_filter]; exact ⟨hr, rfl⟩)
      simp only [hFix, mem_filter, mem_univ, true_and] at this
      exact this
    · intro r hr r' hr' heq
      simp only [mem_coe] at hr hr'
      have h1 := (he (rk κ d (s r))).1 r (by rw [mem_filter]; exact ⟨hr, rfl⟩)
      have h2 := (he (rk κ d (s r'))).1 r' (by rw [mem_filter]; exact ⟨hr', rfl⟩)
      simp only [hFix, mem_filter, mem_univ, true_and] at h1 h2
      simp only at heq
      have hk : rk κ d (s r) = rk κ d (s r') := by rw [← h1.2.1, ← h2.2.1, heq]
      rw [← hk] at heq
      exact (he (rk κ d (s r))).2 (by simp only [coe_filter]; exact ⟨hr, rfl⟩)
        (by simp only [coe_filter]; exact ⟨hr', hk.symm⟩) heq
  have hsgr : ∀ r ∈ SwM, s r - s (g r) < κ / d := by
    intro r hr
    exact hsame r (g r) (hgfix r hr).2.1.symm
  ------------------------------------------------------------------
  -- received fixed items
  ------------------------------------------------------------------
  set Rcv := SwM.image g with hRcv
  obtain ⟨hinv, hinv1⟩ : ∃ h : Fin N → Fin N, ∀ f ∈ Rcv, h f ∈ SwM ∧ g (h f) = f := by
    refine ⟨fun f => if hf : ∃ r ∈ SwM, g r = f then hf.choose else f, ?_⟩
    intro f hf
    rw [hRcv, mem_image] at hf
    simp only [hf, dif_pos]
    exact hf.choose_spec
  have hinvg : ∀ r ∈ SwM, hinv (g r) = r := by
    intro r hr
    have := hinv1 (g r) (mem_image_of_mem _ hr)
    exact hginj this.1 hr this.2
  have hRcvM : ∀ f ∈ Rcv, f ∉ M := by
    intro f hf hfM
    rw [hRcv, mem_image] at hf
    obtain ⟨r, hr, rfl⟩ := hf
    exact ((hMmem _).mp hfM).2 (hgfix r hr).1
  have hRcvP1 : ∀ f ∈ Rcv, ∃ w ∈ V', P1 f = some w := by
    intro f hf
    rw [hRcv, mem_image] at hf
    obtain ⟨r, hr, rfl⟩ := hf
    exact ⟨_, hvkV' r (hSwM_M hr), (hgfix r hr).2.2⟩
  have hRcvy : ∀ f ∈ Rcv, y (hinv f) ∉ V' := by
    intro f hf
    exact ((hSwmem _).mp (hinv1 f hf).1).2.1
  ------------------------------------------------------------------
  -- the assignment after the swaps
  ------------------------------------------------------------------
  obtain ⟨Q, hQ⟩ : ∃ Q : Asg N b, ∀ r, Q r = if r ∈ SwM then some (vk (rk κ d (s r)))
      else if r ∈ Rcv then some (y (hinv r)) else if r ∈ M then some (y r) else P1 r :=
    ⟨_, fun _ => rfl⟩
  have hQSw : ∀ r ∈ SwM, Q r = some (vk (rk κ d (s r))) := by
    intro r hr; rw [hQ, if_pos hr]
  have hQRcv : ∀ r ∈ Rcv, Q r = some (y (hinv r)) := by
    intro r hr
    have : r ∉ SwM := fun h => hRcvM r hr (hSwM_M h)
    rw [hQ, if_neg this, if_pos hr]
  have hQM : ∀ r ∈ M, r ∉ SwM → Q r = some (y r) := by
    intro r hr hr'
    have : r ∉ Rcv := fun h => hRcvM r h hr
    rw [hQ, if_neg hr', if_neg this, if_pos hr]
  have hQo : ∀ r, r ∉ M → r ∉ Rcv → Q r = P1 r := by
    intro r hr hr'
    have : r ∉ SwM := fun h => hr (hSwM_M h)
    rw [hQ, if_neg this, if_neg hr', if_neg hr]
  obtain ⟨I, hImem⟩ : ∃ I : Finset (Fin N), ∀ r, r ∈ I ↔ ∃ w ∈ V', Q r = some w :=
    ⟨univ.filter (fun r => ∃ w ∈ V', Q r = some w), fun r => by simp⟩
  have hISw : ∀ r ∈ SwM, r ∈ I := fun r hr =>
    (hImem r).mpr ⟨_, hvkV' r (hSwM_M hr), hQSw r hr⟩
  have hIRcv : ∀ r ∈ Rcv, r ∉ I := by
    intro r hr hrI
    obtain ⟨w, hw, hQw⟩ := (hImem r).mp hrI
    rw [hQRcv r hr, Option.some.injEq] at hQw
    exact hRcvy r hr (hQw ▸ hw)
  have hIM : ∀ r ∈ M, r ∉ SwM → (r ∈ I ↔ y r ∈ V') := by
    intro r hr hr'
    rw [hImem, hQM r hr hr']
    constructor
    · rintro ⟨w, hw, hQw⟩; rw [Option.some.injEq] at hQw; exact hQw ▸ hw
    · intro h; exact ⟨_, h, rfl⟩
  have hIo : ∀ r, r ∉ M → r ∉ Rcv → (r ∈ I ↔ ∃ w ∈ V', P1 r = some w) := by
    intro r hr hr'
    rw [hImem, hQo r hr hr']
  ------------------------------------------------------------------
  -- basic sums
  ------------------------------------------------------------------
  have hloadP1 : ∀ v, load s P1 v = ∑ r, (if r ∉ M ∧ P1 r = some v then s r else 0) +
      ∑ r ∈ M.filter (fun r => P1 r = some v), s r := by
    intro v
    unfold load
    rw [sum_filter_univ, ← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    by_cases h : r ∈ M <;> simp [h]
  have hRcvsum : ∀ (p : Fin N → Prop) [DecidablePred p],
      ∑ r, (if r ∈ Rcv ∧ p (hinv r) then s r else 0) =
        ∑ r ∈ SwM.filter p, s (g r) := by
    intro p _
    have e : (univ.filter fun r => r ∈ Rcv ∧ p (hinv r)) = (SwM.filter p).image g := by
      ext f
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨hf, hp⟩
        exact ⟨hinv f, ⟨(hinv1 f hf).1, hp⟩, (hinv1 f hf).2⟩
      · rintro ⟨r, ⟨hr, hp⟩, rfl⟩
        refine ⟨mem_image_of_mem _ hr, ?_⟩
        rw [hinvg r hr]; exact hp
    rw [← sum_filter, e, sum_image]
    intro r hr r' hr' heq
    exact hginj (mem_filter.mp hr).1 (mem_filter.mp hr').1 heq
  ------------------------------------------------------------------
  -- the mass labelled in `V'`
  ------------------------------------------------------------------
  have hmass : ∑ r ∈ I, s r ≤ ∑ v ∈ V', T v := by
    have hpt : ∀ r, (if r ∈ I then s r else 0) + (if r ∈ Rcv ∧ True then s r else 0) =
        (if r ∈ SwM then s r else 0) +
        ∑ v ∈ V', (if r ∉ M ∧ P1 r = some v then s r else 0) +
        ∑ v ∈ V', (if r ∈ M ∧ y r = v then s r else 0) := by
      intro r
      rw [sum_ite_and_some, sum_ite_and_eq]
      by_cases h1 : r ∈ SwM
      · have hrM := hSwM_M h1
        have hrR : r ∉ Rcv := fun h => hRcvM r h hrM
        have hyV : y r ∉ V' := ((hSwmem r).mp h1).2.1
        simp [hISw r h1, h1, hrR, hrM, hyV]
      · by_cases h2 : r ∈ Rcv
        · have hrM := hRcvM r h2
          simp [hIRcv r h2, h1, h2, hrM, hRcvP1 r h2]
        · by_cases h3 : r ∈ M
          · by_cases h4 : y r ∈ V'
            · simp [(hIM r h3 h1).mpr h4, h1, h2, h3, h4]
            · have : r ∉ I := fun h => h4 ((hIM r h3 h1).mp h)
              simp [this, h1, h2, h3, h4]
          · by_cases h4 : ∃ w ∈ V', P1 r = some w
            · simp only [(hIo r h3 h2).mpr h4, h1, h2, h3, h4, if_true, if_false, and_true,
                not_false_eq_true, false_and]
              ring
            · have : r ∉ I := fun h => h4 ((hIo r h3 h2).mp h)
              simp only [this, h1, h2, h3, h4, if_false, and_true, not_false_eq_true,
                true_and, false_and]
              ring
    have hsum := congrArg (fun F => F) (sum_congr rfl (fun r (_ : r ∈ univ) => hpt r))
    simp only [sum_add_distrib] at hsum
    rw [← sum_mem_univ, hRcvsum (fun _ => True), ← sum_mem_univ, sum_comm,
      sum_comm (s := univ) (t := V')] at hsum
    have hfilt : SwM.filter (fun _ => True) = SwM := filter_true_of_mem (fun _ _ => trivial)
    rw [hfilt] at hsum
    -- the swap loss
    have hloss : ∑ r ∈ SwM, s r - ∑ r ∈ SwM, s (g r) ≤ ((b - 1 : ℕ) : ℝ) * (κ / d) := by
      rw [← sum_sub_distrib]
      calc ∑ r ∈ SwM, (s r - s (g r)) ≤ ∑ r ∈ SwM, κ / d :=
            sum_le_sum (fun r hr => (hsgr r hr).le)
        _ = SwM.card * (κ / d) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ((b - 1 : ℕ) : ℝ) * (κ / d) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hSwcard
    -- the cycle gain
    have hgain : ∀ v, ∑ r, (if r ∈ M ∧ y r = v then s r else 0) ≤
        ∑ r ∈ M.filter (fun r => P1 r = some v), s r +
        max 0 (∑ r ∈ M.filter (fun r => y r = v), s r - ∑ r ∈ M, s r * z r v) := by
      intro v
      rw [← sum_filter_univ, ← hzload v]
      have := le_max_right 0 (∑ r ∈ M.filter (fun r => y r = v), s r - ∑ r ∈ M, s r * z r v)
      linarith
    have hgainsum : ∑ v ∈ V', ∑ r, (if r ∈ M ∧ y r = v then s r else 0) ≤
        ∑ v ∈ V', ∑ r ∈ M.filter (fun r => P1 r = some v), s r + ((b - 1 : ℕ) : ℝ) * (κ / d) := by
      calc _ ≤ ∑ v ∈ V', (∑ r ∈ M.filter (fun r => P1 r = some v), s r +
            max 0 (∑ r ∈ M.filter (fun r => y r = v), s r - ∑ r ∈ M, s r * z r v)) :=
            sum_le_sum (fun v _ => hgain v)
        _ = _ + ∑ v ∈ V', max 0 (∑ r ∈ M.filter (fun r => y r = v), s r -
            ∑ r ∈ M, s r * z r v) := sum_add_distrib
        _ ≤ _ := by
          apply add_le_add le_rfl
          calc _ ≤ ∑ v, max 0 (∑ r ∈ M.filter (fun r => y r = v), s r -
                ∑ r ∈ M, s r * z r v) :=
                sum_le_univ_sum_of_nonneg (fun v => le_max_left _ _)
            _ ≤ _ := hy5
            _ ≤ _ := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact_mod_cast hu
    have hP1V' : ∑ v ∈ V', load s P1 v = ∑ v ∈ V', ∑ r, (if r ∉ M ∧ P1 r = some v then s r else 0)
        + ∑ v ∈ V', ∑ r ∈ M.filter (fun r => P1 r = some v), s r := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun v _ => hloadP1 v)
    have hslack' : ∑ v ∈ V', load s P1 v + 2 * d * κ ≤ ∑ v ∈ V', T v := by
      have h1 : ∑ v ∈ V, (T v - load s P1 v) ≤ ∑ v ∈ V', (T v - load s P1 v) :=
        sum_le_sum_of_subset_of_nonneg hVV' (fun v _ _ => sub_nonneg.mpr (hP1 v))
      simp only [sum_sub_distrib] at h1 hslack
      linarith
    have hbd' : ((b - 1 : ℕ) : ℝ) * (κ / d) ≤ d * κ := by
      have : ((b - 1 : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 := by
        have : b - 1 ≤ d ^ 2 := by omega
        exact_mod_cast this
      rw [mul_div_assoc', div_le_iff₀ hdpos]
      nlinarith
    linarith
  ------------------------------------------------------------------
  -- repack the bins of `V'`
  ------------------------------------------------------------------
  have hT0 : ∀ v, 0 ≤ T v := by
    intro v
    refine le_trans ?_ (hP1 v)
    unfold load
    exact sum_nonneg (fun r _ => by split_ifs <;> [exact (hpos r).le; exact le_refl 0])
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := repack s hpos T V'.toList (nodup_toList V')
    (fun v _ => hT0 v) I (by rw [sum_map_toList]; exact hmass)
  have hR3' : (I.filter (fun r => R r = none)).card ≤ 3 * d := by
    rw [length_toList] at hR3; omega
  obtain ⟨P', hP'⟩ : ∃ P' : Asg N b, ∀ r, P' r = if r ∈ I then R r else Q r :=
    ⟨_, fun _ => rfl⟩
  have hP'I : ∀ r ∈ I, P' r = R r := fun r hr => by rw [hP', if_pos hr]
  have hP'nI : ∀ r ∉ I, P' r = Q r := fun r hr => by rw [hP', if_neg hr]
  refine ⟨P', ?_, ?_, ?_⟩
  ------------------------------------------------------------------
  -- loads
  ------------------------------------------------------------------
  · intro v
    by_cases hv : v ∈ V'
    · have e : load s P' v = ∑ r ∈ I.filter (fun r => R r = some v), s r := by
        unfold load
        rw [← sum_filter]
        congr 1
        ext r
        simp only [mem_filter, mem_univ, true_and]
        by_cases hr : r ∈ I
        · rw [hP'I r hr]; exact ⟨fun h => ⟨hr, h⟩, fun h => h.2⟩
        · rw [hP'nI r hr]
          constructor
          · intro h; exact absurd ((hImem r).mpr ⟨v, hv, h⟩) hr
          · intro h; exact absurd h.1 hr
      rw [e]
      exact hR2 v (mem_toList.mpr hv)
    · have e1 : load s P' v = load s Q v := by
        unfold load
        apply sum_congr rfl
        intro r _
        by_cases hr : r ∈ I
        · rw [hP'I r hr]
          obtain ⟨w, hw, hQw⟩ := (hImem r).mp hr
          have h1 : R r ≠ some v := fun h => hv (mem_toList.mp (hR1 r hr v h))
          have h2 : Q r ≠ some v := by
            rw [hQw]; intro h; rw [Option.some.injEq] at h; exact hv (h ▸ hw)
          simp [h1, h2]
        · rw [hP'nI r hr]
      have e2 : load s Q v = ∑ r, (if r ∉ M ∧ P1 r = some v then s r else 0) +
          ∑ r, (if r ∈ M ∧ (r ∉ SwM ∧ y r = v) then s r else 0) +
          ∑ r, (if r ∈ Rcv ∧ y (hinv r) = v then s r else 0) := by
        unfold load
        rw [← sum_add_distrib, ← sum_add_distrib]
        apply sum_congr rfl
        intro r _
        by_cases h1 : r ∈ SwM
        · have hrM := hSwM_M h1
          have hrR : r ∉ Rcv := fun h => hRcvM r h hrM
          have : vk (rk κ d (s r)) ≠ v := fun e => hv (e ▸ hvkV' r hrM)
          simp [hQSw r h1, h1, hrR, hrM, this]
        · by_cases h2 : r ∈ Rcv
          · have hrM := hRcvM r h2
            obtain ⟨w, hw, hPw⟩ := hRcvP1 r h2
            have : w ≠ v := fun e => hv (e ▸ hw)
            simp [hQRcv r h2, h2, hrM, hPw, this]
          · by_cases h3 : r ∈ M
            · simp [hQM r h3 h1, h1, h2, h3]
            · simp [hQo r h3 h2, h2, h3]
      have e3 : ∑ r, (if r ∈ M ∧ (r ∉ SwM ∧ y r = v) then s r else 0) =
          ∑ k ∈ range d, ∑ r ∈ A v k \ (A v k).filter (· ∈ SwM), s r := by
        rw [← sum_filter_univ, ← sum_fiberwise_of_maps_to
          (s := M.filter (fun r => r ∉ SwM ∧ y r = v)) (t := range d)
          (g := fun r => rk κ d (s r))
          (fun r hr => mem_range.mpr (hMrk r (mem_filter.mp hr).1))]
        apply sum_congr rfl
        intro k _
        apply sum_congr _ (fun _ _ => rfl)
        ext r
        simp only [mem_filter, mem_sdiff, hAmem]
        tauto
      have e4 : ∑ r, (if r ∈ Rcv ∧ y (hinv r) = v then s r else 0) =
          ∑ k ∈ range d, ∑ r ∈ (A v k).filter (· ∈ SwM), s (g r) := by
        have := hRcvsum (fun r => y r = v)
        rw [this, ← sum_fiberwise_of_maps_to (s := SwM.filter (fun r => y r = v))
          (t := range d) (g := fun r => rk κ d (s r))
          (fun r hr => mem_range.mpr (hMrk r (hSwM_M (mem_filter.mp hr).1)))]
        apply sum_congr rfl
        intro k _
        apply sum_congr _ (fun _ _ => rfl)
        ext r
        simp only [mem_filter, hAmem]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨hSwM_M h1, h3, h2⟩, h1⟩
        · rintro ⟨⟨_, h3, h2⟩, h1⟩; exact ⟨⟨h1, h2⟩, h3⟩
      have e5 : ∀ k ∈ range d, ∑ r ∈ A v k \ (A v k).filter (· ∈ SwM), s r +
          ∑ r ∈ (A v k).filter (· ∈ SwM), s (g r) ≤
          ∑ r ∈ M.filter (fun r => rk κ d (s r) = k), s r * z r v := by
        intro k _
        apply threshold (A v k) ((A v k).filter (· ∈ SwM))
          (M.filter (fun r => rk κ d (s r) = k)) s (fun r => z r v) (fun r => s (g r))
          (filter_subset _ _)
        · intro r hr
          rw [hAmem] at hr
          exact mem_filter.mpr ⟨hr.1, hr.2.1⟩
        · intro r _; exact hz0 r v
        · intro x hx r hr
          rw [mem_filter, hAmem] at hx
          rw [mem_filter] at hr
          have hfx := hgfix x hx.2
          have := fixed_lt_movable s κ d P1 (g x) r hfx.1 hr.1
            (by rw [hfx.2.1, hx.1.2.1, hr.2])
          exact (hs this).le
        · rw [hAeq]; exact hy2 v k
        · intro θ
          set Kp := ((A v k) \ (A v k).filter (· ∈ SwM)).filter (fun x => θ ≤ s x) with hKp
          rcases Kp.eq_empty_or_nonempty with he | hne
          · rw [he, card_empty, Nat.cast_zero]
            exact sum_nonneg (fun r _ => hz0 r v)
          · have hx0 := min'_mem Kp hne
            set x0 := Kp.min' hne
            rw [hKp, mem_filter, mem_sdiff, mem_filter, hAmem] at hx0
            obtain ⟨⟨⟨hx0M, hx0k, hx0y⟩, hx0n⟩, hx0θ⟩ := hx0
            have hx0Sw : x0 ∉ SwM := fun h =>
              hx0n ⟨⟨hx0M, hx0k, hx0y⟩, h⟩
            have hrank : u v k ≤ ((A v k).filter (· < x0)).card := by
              by_contra hlt
              push Not at hlt
              apply hx0Sw
              rw [hSwmem]
              refine ⟨hx0M, by rw [hx0y]; exact hv, ?_⟩
              rw [hx0y, hx0k]
              exact hlt
            have hdisj : Disjoint ((A v k).filter (· < x0)) Kp := by
              rw [disjoint_left]
              intro p hp hpK
              rw [mem_filter] at hp
              exact absurd (min'_le Kp p hpK) (not_le.mpr hp.2)
            have hsub : (A v k).filter (· < x0) ∪ Kp ⊆ (A v k).filter (fun x => θ ≤ s x) := by
              intro p hp
              rcases mem_union.mp hp with hp | hp
              · rw [mem_filter] at hp ⊢
                exact ⟨hp.1, le_trans hx0θ (hs hp.2).le⟩
              · rw [hKp, mem_filter, mem_sdiff] at hp
                rw [mem_filter]
                exact ⟨hp.1.1, hp.2⟩
            have hc := card_le_card hsub
            rw [card_union_of_disjoint hdisj] at hc
            have h4 := hy4 v k θ
            have e1' : (A v k).filter (fun x => θ ≤ s x) =
                M.filter (fun r => rk κ d (s r) = k ∧ y r = v ∧ θ ≤ s r) := by
              rw [hAeq, filter_filter]
              apply filter_congr
              intro r _
              exact and_assoc
            have e2' : (M.filter (fun r => rk κ d (s r) = k)).filter (fun r => θ ≤ s r) =
                M.filter (fun r => rk κ d (s r) = k ∧ θ ≤ s r) := filter_filter _ _ _
            rw [e2']
            rw [← e1'] at h4
            have hc' : (Kp.card : ℝ) + u v k ≤ ((A v k).filter (fun x => θ ≤ s x)).card := by
              exact_mod_cast (by omega : Kp.card + u v k ≤ _)
            linarith
      have e6 : ∑ k ∈ range d, ∑ r ∈ M.filter (fun r => rk κ d (s r) = k), s r * z r v =
          ∑ r ∈ M, s r * z r v :=
        sum_fiberwise_of_maps_to (fun r hr => mem_range.mpr (hMrk r hr)) _
      have h7 := sum_le_sum e5
      rw [sum_add_distrib, e6, hzload v] at h7
      have h8 := hP1 v
      rw [hloadP1 v] at h8
      rw [e1, e2, e3, e4]
      linarith
  ------------------------------------------------------------------
  -- exclusions
  ------------------------------------------------------------------
  · unfold excl
    have hsub : univ.filter (fun r => P' r = none) ⊆
        univ.filter (fun r => P1 r = none) ∪ I.filter (fun r => R r = none) := by
      intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      rw [mem_union, mem_filter, mem_filter]
      by_cases hrI : r ∈ I
      · right; exact ⟨hrI, by rw [← hP'I r hrI]; exact hr⟩
      · left
        refine ⟨mem_univ _, ?_⟩
        rw [hP'nI r hrI] at hr
        by_cases h1 : r ∈ SwM
        · rw [hQSw r h1] at hr; simp at hr
        by_cases h2 : r ∈ Rcv
        · rw [hQRcv r h2] at hr; simp at hr
        by_cases h3 : r ∈ M
        · rw [hQM r h3 h1] at hr; simp at hr
        rw [hQo r h3 h2] at hr
        exact hr
    have h1 := card_le_card hsub
    have h2 := card_union_le (univ.filter (fun r => P1 r = none)) (I.filter (fun r => R r = none))
    omega
  ------------------------------------------------------------------
  -- changes
  ------------------------------------------------------------------
  · set S := ((univ.filter (fun r => P1 r = none) ∪ univ.filter (fun r => IsFixed s κ d P1 r)) ∪
      SwM) ∪ I.filter (fun r => R r = none) with hS
    have hfixcard : (univ.filter (fun r => IsFixed s κ d P1 r)).card ≤ d * (b * (b - 1)) := by
      rw [card_eq_sum_card_fiberwise (f := fun r => rk κ d (s r)) (t := range d)
        (fun r hr => mem_range.mpr (hrkd r (mem_filter.mp hr).2.1))]
      calc _ ≤ ∑ k ∈ range d, b * (b - 1) := by
            apply sum_le_sum
            intro k _
            rw [filter_filter]
            exact card_fixed_range_le s κ d P1 k
        _ = _ := by simp
    have hScard : S.card ≤ excl P1 + d * (b * (b - 1)) + (b - 1) + 3 * d := by
      have h1 := card_union_le ((univ.filter (fun r => P1 r = none) ∪
        univ.filter (fun r => IsFixed s κ d P1 r)) ∪ SwM) (I.filter (fun r => R r = none))
      have h2 := card_union_le (univ.filter (fun r => P1 r = none) ∪
        univ.filter (fun r => IsFixed s κ d P1 r)) SwM
      have h3 := card_union_le (univ.filter (fun r => P1 r = none))
        (univ.filter (fun r => IsFixed s κ d P1 r))
      rw [← hS] at h1
      unfold excl
      omega
    set S1 := univ.filter (fun r : Fin N => ∃ h : r.val + 1 < N, (⟨r.val + 1, h⟩ : Fin N) ∈ S)
      with hS1
    have hS1card : S1.card ≤ S.card := by
      apply card_le_card_of_injOn nx
      · intro r hr
        simp only [hS1, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr
        obtain ⟨h, hh⟩ := hr
        rw [mem_coe, nx_eq r h]
        exact hh
      · intro r hr r' hr' heq
        simp only [hS1, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr hr'
        obtain ⟨h, -⟩ := hr
        obtain ⟨h', -⟩ := hr'
        rw [nx_eq r h, nx_eq r' h'] at heq
        rw [Fin.mk.injEq] at heq
        exact Fin.ext (by omega)
    set Ych := univ.filter (fun r : Fin N => ∃ h : r.val + 1 < N, r ∈ M ∧
      (⟨r.val + 1, h⟩ : Fin N) ∈ M ∧ y r ≠ y ⟨r.val + 1, h⟩) with hYch
    have hYcard : Ych.card ≤ d + d * (b * b) := by
      apply ychanges_le M (fun r => rk κ d (s r)) d y
      · intro r _ r' _ h; exact hrkanti r r' h
      · exact hMrk
      · intro r1 h1 r2 h2 r3 h3 r4 h4 h12 h23 h34 hf hy13 hy24 hne
        have e12 := hrkanti r1 r2 h12.le
        have e23 := hrkanti r2 r3 h23.le
        have e34 := hrkanti r3 r4 h34.le
        have a1 := hord (y r1) (y r2) r3 h3 r2 h2 r1 h1 (by omega) (by omega) (hs h23) (hs h12)
          (by rw [hy13]; exact hy1 r3 h3) (hy1 r2 h2) (hy1 r1 h1) hne
        have a2 := hord (y r2) (y r1) r4 h4 r3 h3 r2 h2 (by omega) (by omega) (hs h34) (hs h23)
          (by rw [hy24]; exact hy1 r4 h4) (by rw [hy13]; exact hy1 r3 h3) (hy1 r2 h2)
          (Ne.symm hne)
        exact lt_asymm a1 a2
    have hCsub : univ.filter (fun r : Fin N => ∃ h : r.val + 1 < N, P' r ≠ P' ⟨r.val + 1, h⟩) ⊆
        (S ∪ S1) ∪ Ych := by
      intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      obtain ⟨h, hne⟩ := hr
      by_cases hS' : r ∈ S
      · exact mem_union_left _ (mem_union_left _ hS')
      by_cases hS1' : (⟨r.val + 1, h⟩ : Fin N) ∈ S
      · exact mem_union_left _ (mem_union_right _ (by rw [hS1, mem_filter]; exact ⟨mem_univ _, h, hS1'⟩))
      apply mem_union_right
      rw [hYch, mem_filter]
      refine ⟨mem_univ _, h, ?_⟩
      have key : ∀ x, x ∉ S → x ∈ M ∧ x ∉ SwM ∧ ¬ (x ∈ I ∧ R x = none) := by
        intro x hx
        simp only [hS, mem_union, mem_filter, mem_univ, true_and, not_or] at hx
        exact ⟨(hMmem x).mpr ⟨hx.1.1.1, hx.1.1.2⟩, hx.1.2, hx.2⟩
      obtain ⟨hrM, hrSw, hrI⟩ := key r hS'
      obtain ⟨hr'M, hr'Sw, hr'I⟩ := key _ hS1'
      refine ⟨hrM, hr'M, ?_⟩
      intro hyeq
      apply hne
      by_cases hyV : y r ∈ V'
      · have h1 : r ∈ I := (hIM r hrM hrSw).mpr hyV
        have h2 : (⟨r.val + 1, h⟩ : Fin N) ∈ I := (hIM _ hr'M hr'Sw).mpr (hyeq ▸ hyV)
        rw [hP'I r h1, hP'I _ h2]
        exact hR4 r h1 h h2 (fun e => hrI ⟨h1, e⟩) (fun e => hr'I ⟨h2, e⟩)
      · have h1 : r ∉ I := fun hh => hyV ((hIM r hrM hrSw).mp hh)
        have h2 : (⟨r.val + 1, h⟩ : Fin N) ∉ I := by
          intro hh
          apply hyV
          rw [hyeq]
          exact (hIM _ hr'M hr'Sw).mp hh
        rw [hP'nI r h1, hP'nI _ h2, hQM r hrM hrSw, hQM _ hr'M hr'Sw, hyeq]
    unfold changes
    have h1 := card_le_card hCsub
    have h5 := card_union_le (S ∪ S1) Ych
    have h6 := card_union_le S S1
    have hb1 : b * (b - 1) ≤ b * b := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hb2 : d * (b * (b - 1)) ≤ d * (b * b) := Nat.mul_le_mul_left _ hb1
    have hb3 : b - 1 ≤ b := Nat.sub_le _ _
    have hfin : 2 * (excl P1 + d * (b * b) + b + 3 * d) + (d + d * (b * b)) ≤
        2 * excl P1 + 20 * d * (b + 1) ^ 2 := by
      nlinarith [Nat.mul_le_mul_right b hd]
    linarith

end SublinearChoresMMS.Dev.Rearr.PartFin
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
alias finish := SublinearChoresMMS.Dev.Rearr.PartFin.finish

end SublinearChoresMMS.Dev.Rearr
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr.PartCore
open SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
lemma changes_none (P : Asg N b) (h : ∀ r, P r = none) : changes P = 0 := by
  unfold changes
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro r - ⟨_, hne⟩
  exact hne (by rw [h, h])

/-- Two sizes in `(0, κ]` with the same range index differ by less than `κ / d`. -/
lemma rk_diff (κ : ℝ) (hκ : 0 < κ) (d : ℕ) (hd : 1 ≤ d) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : rk κ d x = rk κ d y) : x - y ≤ κ / d := by
  unfold rk at h
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hxa : 0 < x * d / κ := by positivity
  have hya : 0 < y * d / κ := by positivity
  have h1 : 1 ≤ ⌈x * d / κ⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : 1 ≤ ⌈y * d / κ⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have heq : ⌈x * d / κ⌉₊ = ⌈y * d / κ⌉₊ := by omega
  have hx1 : x * d / κ ≤ ⌈x * d / κ⌉₊ := Nat.le_ceil _
  have hy1 : (⌈y * d / κ⌉₊ : ℝ) < y * d / κ + 1 := Nat.ceil_lt_add_one hya.le
  rw [heq] at hx1
  have : (x - y) * d / κ ≤ 1 := by
    have : (x - y) * d / κ = x * d / κ - y * d / κ := by ring
    linarith
  rw [div_le_iff₀ hκ, one_mul] at this
  rw [le_div_iff₀ hdpos]
  linarith

theorem core (N b d : ℕ) (hd : 1 ≤ d) (hbd : b ≤ d ^ 2) (s : Fin N → ℝ) (hs : StrictAnti s)
    (hpos : ∀ r, 0 < s r) (T : Fin b → ℝ) (P : Asg N b) (hP : ∀ v, load s P v ≤ T v) :
    ∃ P' : Asg N b, (∀ v, load s P' v ≤ T v) ∧ excl P' ≤ excl P + 5 * d ∧
      changes P' ≤ 2 * excl P + 25 * d * (b + 1) ^ 2 := by
  obtain ⟨P1, κ, V, hκ0, hV, hP1P, hex1, hsmall, hslack, hP1⟩ :=
    SublinearChoresMMS.Dev.Rearr.step1 N b d s hs hpos T P hP
  by_cases hall : ∀ r, P1 r = none
  · exact ⟨P1, hP1, hex1.trans (by omega), by rw [changes_none P1 hall]; exact Nat.zero_le _⟩
  push Not at hall
  obtain ⟨r0, hr0⟩ := hall
  obtain ⟨v0, -⟩ := Option.ne_none_iff_exists'.mp hr0
  have hb : 0 < b := Fin.pos v0
  have hκ : 0 < κ := (hpos r0).trans_le (hsmall r0 hr0)
  set Mv := movable s κ d P1 with hMv
  set y0 : Fin N → Fin b := fun r => (P1 r).getD ⟨0, hb⟩ with hy0
  have hMvne : ∀ r ∈ Mv, P1 r ≠ none := fun r hr => (mem_filter.mp hr).2.1
  have hy0iff : ∀ r ∈ Mv, ∀ v, y0 r = v ↔ P1 r = some v := by
    intro r hr v
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (hMvne r hr)
    simp [hy0, hw]
  obtain ⟨z, hz0, hzout, hz1, hzc, hzload, hord, hbasic⟩ :=
    SublinearChoresMMS.Dev.Rearr.lp_basic s Mv (fun r => rk κ d (s r)) y0
  have hW : ∀ r1 ∈ Mv, ∀ r2 ∈ Mv, (fun r => rk κ d (s r)) r1 = (fun r => rk κ d (s r)) r2 →
      s r1 - s r2 ≤ κ / d := fun r1 _ r2 _ h => rk_diff κ hκ d hd _ _ (hpos r1) (hpos r2) h
  obtain ⟨y, u, hy1, hy2, hu, hy4, hy5⟩ :=
    SublinearChoresMMS.Dev.Rearr.round hb s hs Mv (fun r => rk κ d (s r)) (κ / d) hW z hz0
      hzout hz1 (fun v k => ⟨_, hzc v k⟩) hord hbasic
  have hzload' : ∀ v, ∑ r ∈ Mv, s r * z r v = ∑ r ∈ Mv.filter (fun r => P1 r = some v), s r := by
    intro v
    rw [hzload v]
    congr 1
    exact filter_congr fun r hr => hy0iff r hr v
  have hzc' : ∀ v k, ∑ r ∈ Mv.filter (fun r => rk κ d (s r) = k), z r v =
      ((Mv.filter fun r => rk κ d (s r) = k ∧ P1 r = some v).card : ℝ) := by
    intro v k
    rw [hzc v k]
    congr 2
    exact filter_congr fun r hr => and_congr_right fun _ => hy0iff r hr v
  obtain ⟨P', hP', hex', hch'⟩ :=
    SublinearChoresMMS.Dev.Rearr.finish N b d hd hbd s hs hpos T P1 hP1 κ hκ V hV hsmall hslack
      z y u hzout hzload' hzc' hz0 hord hy1 hy2 hu hy4 hy5
  refine ⟨P', hP', by omega, ?_⟩
  have h1 : 1 ≤ (b + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 4 * d ≤ 5 * d * (b + 1) ^ 2 := by nlinarith
  nlinarith

end SublinearChoresMMS.Dev.Rearr.PartCore
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Dev.Rearr
variable {N b : ℕ}
alias core := SublinearChoresMMS.Dev.Rearr.PartCore.core

end SublinearChoresMMS.Dev.Rearr
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Disposal.PartAd
open SublinearChoresMMS.Disposal SublinearChoresMMS.Dev.Rearr
lemma sum_shift {M : ℕ} (hM : 1 ≤ M) (g : Fin M → ℝ) :
    ∑ r, g r = g ⟨0, hM⟩ + ∑ j : Fin (M - 1), g ⟨j.val + 1, by omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  rfl

/-- The generic transfer from labels with a dummy representative `0` to `core`. -/
lemma transfer {M B : ℕ} (hM : 1 ≤ M) (g : Fin M → ℝ)
    (hg : StrictAnti fun j : Fin (M - 1) => g ⟨j.val + 1, by omega⟩)
    (hgpos : ∀ r, 0 < g r) (T : Fin B → ℝ) (p : Fin M → Option (Fin B))
    (hp0 : ∀ r : Fin M, r.val = 0 → p r = none)
    (hp : ∀ v, (∑ r, if p r = some v then g r else 0) ≤ T v) (d : ℕ) (hd : 1 ≤ d)
    (hbd : B ≤ d ^ 2) :
    ∃ p' : Fin M → Option (Fin B), (∀ r : Fin M, r.val = 0 → p' r = none) ∧
      (∀ v, (∑ r, if p' r = some v then g r else 0) ≤ T v) ∧
      (univ.filter fun r : Fin M => 0 < r.val ∧ p' r = none).card ≤
        (univ.filter fun r : Fin M => 0 < r.val ∧ p r = none).card + 5 * d ∧
      (univ.filter fun r : Fin M =>
          ∃ h : 0 < r.val, 1 < r.val ∧ p' r ≠ p' ⟨r.val - 1, by omega⟩).card ≤
        2 * (univ.filter fun r : Fin M => 0 < r.val ∧ p r = none).card +
          25 * d * (B + 1) ^ 2 := by
  set s : Fin (M - 1) → ℝ := fun j => g ⟨j.val + 1, by omega⟩ with hs
  set P : Asg (M - 1) B := fun j => p ⟨j.val + 1, by omega⟩ with hP
  have hload : ∀ (Q : Asg (M - 1) B) (p' : Fin M → Option (Fin B)), p' ⟨0, hM⟩ = none →
      (∀ j : Fin (M - 1), p' ⟨j.val + 1, by omega⟩ = Q j) →
      ∀ v, (∑ r, if p' r = some v then g r else 0) = load s Q v := by
    intro Q p' h0 hQ v
    rw [sum_shift hM, h0]
    simp only [reduceCtorEq, if_false, zero_add]
    unfold load
    apply sum_congr rfl
    intro j _
    rw [hQ j]
  have hPv : ∀ v, load s P v ≤ T v := fun v =>
    (hload P p (hp0 _ rfl) (fun j => rfl) v) ▸ hp v
  obtain ⟨P', hP', hex', hch'⟩ :=
    SublinearChoresMMS.Dev.Rearr.core (M - 1) B d hd hbd s hg (fun j => hgpos _) T P hPv
  set p' : Fin M → Option (Fin B) :=
    fun r => if h : r.val = 0 then none else P' ⟨r.val - 1, by omega⟩ with hp'
  have hp'0 : ∀ r : Fin M, r.val = 0 → p' r = none := fun r hr => by simp [hp', hr]
  have hp'succ : ∀ r : Fin M, ∀ j : Fin (M - 1), r.val = j.val + 1 → p' r = P' j := by
    intro r j h
    have hr : r.val ≠ 0 := by omega
    simp only [hp', hr, dif_neg, not_false_eq_true]
    congr 1; ext; simp; omega
  -- excluded counts
  have hexA : (univ.filter fun r : Fin M => 0 < r.val ∧ p' r = none).card ≤ excl P' := by
    unfold excl
    refine (card_le_card ?_).trans (card_image_le (f := fun j : Fin (M - 1) =>
      (⟨j.val + 1, by omega⟩ : Fin M)))
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    simp only [mem_image, mem_filter, mem_univ, true_and]
    refine ⟨⟨r.val - 1, by omega⟩, ?_, ?_⟩
    · rw [← hp'succ r _ (by simp; omega)]; exact hr.2
    · ext; simp; omega
  have hexB : excl P ≤ (univ.filter fun r : Fin M => 0 < r.val ∧ p r = none).card := by
    unfold excl
    rw [← card_image_of_injective _ (f := fun j : Fin (M - 1) =>
      (⟨j.val + 1, by omega⟩ : Fin M)) (by intro a b h; ext; simpa using h)]
    apply card_le_card
    intro r hr
    simp only [mem_image, mem_filter, mem_univ, true_and] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨by simp, hj⟩
  have hseg : (univ.filter fun r : Fin M =>
      ∃ h : 0 < r.val, 1 < r.val ∧ p' r ≠ p' ⟨r.val - 1, by omega⟩).card ≤ changes P' := by
    unfold changes
    refine (card_le_card ?_).trans (card_image_le (f := fun j : Fin (M - 1) =>
      (⟨(j.val + 2) % M, Nat.mod_lt _ (by omega)⟩ : Fin M)))
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    obtain ⟨h0, h1, hne⟩ := hr
    simp only [mem_image, mem_filter, mem_univ, true_and]
    refine ⟨⟨r.val - 2, by omega⟩, ⟨by simp; omega, ?_⟩, ?_⟩
    · rw [hp'succ r ⟨r.val - 2 + 1, by omega⟩ (by simp; omega),
        hp'succ ⟨r.val - 1, by omega⟩ ⟨r.val - 2, by omega⟩ (by simp; omega)] at hne
      exact hne.symm
    · ext; simp; rw [Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨p', hp'0, fun v => ?_, ?_, ?_⟩
  · rw [hload P' p' (hp'0 _ rfl) (fun j => hp'succ _ j rfl)]; exact hP' v
  · omega
  · omega

lemma blockSize_pos (n : ℕ) : 1 ≤ blockSize n := Nat.one_le_two_pow

lemma blockSize_le (n : ℕ) (hn : 2 ≤ n) : blockSize n ≤ n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  set x := Real.sqrt ((n : ℝ) * Real.log n) with hx
  have hxpos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have hxn : x ≤ n := by
    have h1 : Real.log n ≤ n := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < n)]
    calc x ≤ Real.sqrt ((n : ℝ) ^ 2) := by
          apply Real.sqrt_le_sqrt; rw [sq]
          exact mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = n := Real.sqrt_sq (by linarith)
  have key : ((2 : ℝ)) ^ (⌊Real.logb 2 x⌋₊) ≤ n := by
    by_cases h : 0 ≤ Real.logb 2 x
    · calc (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊) = (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℕ) : ℝ) :=
            (Real.rpow_natCast 2 _).symm
        _ ≤ (2 : ℝ) ^ (Real.logb 2 x) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le h)
        _ = x := Real.rpow_logb (by norm_num) (by norm_num) hxpos
        _ ≤ n := hxn
    · push Not at h
      rw [Nat.floor_of_nonpos h.le]; simp; linarith
  unfold blockSize
  rw [← hx]
  exact_mod_cast key

theorem lemma_3_1_rearrangement_dev :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
        blockSize n ≤ m → blockSize n ∣ m →
        ∀ c : Cost n m, Normalized c → ∀ i : Fin n,
          ∀ p : Labels n m (blockSize n), ValidPacking c i p →
          ∃ p' : Labels n m (blockSize n), ValidPacking c i p' ∧
            (excludedCount p' : ℝ) ≤ excludedCount p + A * Real.sqrt (n / blockSize n : ℕ) ∧
            (segments p' : ℝ) ≤ B * ((n / blockSize n : ℕ) ^ 3 + excludedCount p) := by
  refine ⟨15, 2000, by norm_num, by norm_num, 2, le_rfl, ?_⟩
  intro n hn m hqm _ c hc i p hp
  have hq1 := blockSize_pos n
  have hqn := blockSize_le n hn
  have hL : 1 ≤ n / blockSize n := (Nat.one_le_div_iff (by omega)).mpr hqn
  have hM : 1 ≤ m / blockSize n := (Nat.one_le_div_iff (by omega)).mpr hqm
  have hBL : binCount n (blockSize n) ≤ n / blockSize n + 1 := by
    unfold binCount; split_ifs <;> omega
  have hrq : ∀ r : Fin (m / blockSize n), r.val * blockSize n < m := by
    intro r
    have h1 : r.val + 1 ≤ m / blockSize n := r.isLt
    have h2 : (r.val + 1) * blockSize n ≤ m :=
      (Nat.le_div_iff_mul_le (by omega)).mp h1
    nlinarith
  have hrep : ∀ r : Fin (m / blockSize n),
      representativeCost c i (blockSize n) r = c i ⟨r.val * blockSize n, hrq r⟩ := by
    intro r; unfold representativeCost; rw [dif_pos (hrq r)]
  set d := Nat.sqrt (binCount n (blockSize n)) + 1 with hd
  have hbd : binCount n (blockSize n) ≤ d ^ 2 := by
    have := Nat.lt_succ_sqrt' (binCount n (blockSize n)); rw [Nat.succ_eq_add_one] at this; rw [hd]; omega
  have hg : StrictAnti fun j : Fin (m / blockSize n - 1) =>
      representativeCost c i (blockSize n) ⟨j.val + 1, by omega⟩ := by
    intro j j' hjj
    simp only [hrep]
    apply hc.2.1 i
    show (j.val + 1) * blockSize n < (j'.val + 1) * blockSize n
    have : j.val < j'.val := hjj
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have hgpos : ∀ r, 0 < representativeCost c i (blockSize n) r := fun r => by
    rw [hrep]; exact hc.1 _ _
  obtain ⟨p', hp'0, hp'v, hex, hseg⟩ := transfer hM (representativeCost c i (blockSize n)) hg
    hgpos (binCapacity n (blockSize n)) p hp.1 hp.2 d (by omega) hbd
  refine ⟨p', ⟨hp'0, hp'v⟩, ?_, ?_⟩
  · -- exclusions: `5 d ≤ 15 √L`
    set L := n / blockSize n with hLdef
    have hd2 : d ^ 2 ≤ 9 * L := by
      have h := Nat.sqrt_le' (binCount n (blockSize n))
      rw [hd]
      nlinarith
    have hdr : (d : ℝ) ≤ 3 * Real.sqrt L := by
      have : Real.sqrt ((9 : ℝ) * L) = 3 * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num)]
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← this]
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast hd2
    have hexr : (excludedCount p' : ℝ) ≤ excludedCount p + 5 * d := by
      unfold excludedCount; exact_mod_cast hex
    linarith
  · set L := n / blockSize n with hLdef
    set e := excludedCount p with he
    have hsegs : segments p' ≤ 1 + 2 * e + 25 * d * (binCount n (blockSize n) + 1) ^ 2 := by
      unfold segments
      split_ifs
      · exact Nat.zero_le _
      · have := hseg; rw [he]; unfold excludedCount; omega
    have hd6 : d ≤ 6 * L := by
      have h := Nat.sqrt_le' (binCount n (blockSize n))
      rw [hd]
      nlinarith
    have hB3 : binCount n (blockSize n) + 1 ≤ 3 * L := by omega
    have hB9 : (binCount n (blockSize n) + 1) ^ 2 ≤ 9 * L ^ 2 := by
      calc _ ≤ (3 * L) ^ 2 := Nat.pow_le_pow_left hB3 2
        _ = 9 * L ^ 2 := by ring
    have hX : d * (binCount n (blockSize n) + 1) ^ 2 ≤ 54 * L ^ 3 := by
      calc _ ≤ (6 * L) * (9 * L ^ 2) := Nat.mul_le_mul hd6 hB9
        _ = 54 * L ^ 3 := by ring
    have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hnat : segments p' ≤ 2000 * (L ^ 3 + e) := by
      have : 25 * d * (binCount n (blockSize n) + 1) ^ 2 ≤ 25 * (54 * L ^ 3) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ hX
      omega
    have : (segments p' : ℝ) ≤ ((2000 * (L ^ 3 + e) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this
    linarith

end SublinearChoresMMS.Disposal.PartAd
end
end

section
noncomputable section
open Classical Finset
namespace SublinearChoresMMS.Disposal
alias lemma_3_1_rearrangement_dev := SublinearChoresMMS.Disposal.PartAd.lemma_3_1_rearrangement_dev

end SublinearChoresMMS.Disposal
end
end

section
noncomputable section
open Classical Finset
open SublinearChoresMMS
open SublinearChoresMMS.Disposal
theorem solution :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
        blockSize n ≤ m → blockSize n ∣ m →
        ∀ c : Cost n m, Normalized c → ∀ i : Fin n,
          ∀ p : Labels n m (blockSize n), ValidPacking c i p →
          ∃ p' : Labels n m (blockSize n), ValidPacking c i p' ∧
            (excludedCount p' : ℝ) ≤ excludedCount p + A * Real.sqrt (n / blockSize n : ℕ) ∧
            (segments p' : ℝ) ≤ B * ((n / blockSize n : ℕ) ^ 3 + excludedCount p) := by
  exact SublinearChoresMMS.Disposal.lemma_3_1_rearrangement_dev
end
end
