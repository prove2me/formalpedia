-- Prove2me | solution 1 for UCConvexHull.OneUC.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T04:53:20.498515+00:00
-- url     : https://prove2.me/submissions/799f2a8f-a675-4d37-b465-beb3ba388b1f

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_Model

set_option autoImplicit false

namespace UCConvexHull.OneUC.Pf

open UCConvexHull.OneUC

/-- topological potential on the nodes of `G` -/
def pot (U : ThermalUnit) : Node → ℕ
  | .src => 0
  | .snk => 2 * U.n + 3
  | .on t => 2 * t + 1
  | .off t => 2 * t

lemma arc_facts (U : ThermalUnit) (hU : U.Standing) (e : Node × Node) (he : e ∈ arcs U) :
    pot U e.1 < pot U e.2 ∧ pot U e.2 ≤ 2 * U.n + 3 ∧ e.2 ≠ Node.src ∧ e.2 ∈ nodes U := by
  have h1 : 1 ≤ U.τup := hU.1
  unfold arcs at he
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at he
  rcases he with ((((⟨hk, hhk, rfl⟩ | ⟨kr, hkr, rfl⟩) | hs) | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) | rfl
  · simp only [onPairs, periods, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hhk
    refine ⟨?_, ?_, by simp, ?_⟩
    · simp only [pot]; omega
    · simp only [pot]; omega
    · simp [nodes, periods]; omega
  · simp only [offPairs, periods, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hkr
    refine ⟨?_, ?_, by simp, ?_⟩
    · simp only [pot]; omega
    · simp only [pot]; omega
    · simp [nodes, periods]; omega
  · unfold srcArcs at hs
    split_ifs at hs
    · simp only [Finset.mem_image, Finset.mem_filter, periods, Finset.mem_Icc] at hs
      obtain ⟨k, hk, rfl⟩ := hs
      refine ⟨?_, ?_, by simp, ?_⟩
      · simp only [pot]; omega
      · simp only [pot]; omega
      · simp [nodes, periods]; omega
    · simp only [Finset.mem_image, Finset.mem_filter, periods, Finset.mem_Icc] at hs
      obtain ⟨k, hk, rfl⟩ := hs
      refine ⟨?_, ?_, by simp, ?_⟩
      · simp only [pot]; omega
      · simp only [pot]; omega
      · simp [nodes, periods]; omega
  · simp only [periods, Finset.mem_Icc] at ht
    refine ⟨?_, ?_, by simp, ?_⟩
    · simp only [pot]; omega
    · simp only [pot]; omega
    · simp [nodes]
  · simp only [periods, Finset.mem_Icc] at ht
    refine ⟨?_, ?_, by simp, ?_⟩
    · simp only [pot]; omega
    · simp only [pot]; omega
    · simp [nodes]
  · refine ⟨?_, ?_, by simp, ?_⟩
    · simp only [pot]; omega
    · simp only [pot]; omega
    · simp [nodes]

/-- inflow -/
def inF (U : ThermalUnit) (y : arcs U → ℝ) (v : Node) : ℝ := ∑ e : arcs U with e.1.2 = v, y e
/-- outflow -/
def outF (U : ThermalUnit) (y : arcs U → ℝ) (v : Node) : ℝ := ∑ e : arcs U with e.1.1 = v, y e

lemma inF_src (U : ThermalUnit) (hU : U.Standing) (y : arcs U → ℝ) : inF U y Node.src = 0 := by
  unfold inF
  apply Finset.sum_eq_zero
  intro e he
  simp only [Finset.mem_filter] at he
  exact absurd he.2 (arc_facts U hU e.1 e.2).2.2.1

lemma inF_lin (U : ThermalUnit) (a b : ℝ) (y z : arcs U → ℝ) (v : Node) :
    inF U (fun e => a * y e + b * z e) v = a * inF U y v + b * inF U z v := by
  simp [inF, Finset.sum_add_distrib, Finset.mul_sum]

lemma outF_lin (U : ThermalUnit) (a b : ℝ) (y z : arcs U → ℝ) (v : Node) :
    outF U (fun e => a * y e + b * z e) v = a * outF U y v + b * outF U z v := by
  simp [outF, Finset.sum_add_distrib, Finset.mul_sum]

lemma exists_pos_of_sum_pos (U : ThermalUnit) (y : arcs U → ℝ) (p : arcs U → Prop) [DecidablePred p]
    (h : 0 < ∑ e : arcs U with p e, y e) : ∃ e, p e ∧ 0 < y e := by
  by_contra hc
  push Not at hc
  have : ∑ e : arcs U with p e, y e ≤ 0 :=
    Finset.sum_nonpos (fun e he => hc e (Finset.mem_filter.1 he).2)
  linarith

lemma le_inF (U : ThermalUnit) (y : arcs U → ℝ) (hy : ∀ e, 0 ≤ y e) (e : arcs U) :
    y e ≤ inF U y e.1.2 := by
  unfold inF
  exact Finset.single_le_sum (f := y) (fun i _ => hy i) (by simp)

/-- a nonnegative circulation on `G` vanishes -/
lemma circ_zero (U : ThermalUnit) (hU : U.Standing) (c : arcs U → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hc : ∀ u ∈ nodes U, inF U c u = outF U c u) : ∀ e, c e = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨e1, he1⟩ := hne
  have hS : (Finset.univ.filter (fun e : arcs U => c e ≠ 0)).Nonempty := ⟨e1, by simp [he1]⟩
  obtain ⟨e0, he0, hmax⟩ := Finset.exists_max_image _ (fun e : arcs U => pot U e.1.1) hS
  have hce0 : 0 < c e0 := lt_of_le_of_ne (hc0 e0) (Ne.symm (Finset.mem_filter.1 he0).2)
  have hf := arc_facts U hU e0.1 e0.2
  have hin := le_inF U c hc0 e0
  have hout : 0 < outF U c e0.1.2 := by rw [← hc _ hf.2.2.2]; linarith
  obtain ⟨e2, he2, hpos⟩ := exists_pos_of_sum_pos U c _ hout
  have := hmax e2 (by simp [hpos.ne'])
  rw [he2] at this
  omega

/-- a unit path from `v` to the sink inside the support of `y` -/
lemma path_exists (U : ThermalUnit) (hU : U.Standing) (y : arcs U → ℝ) (hy0 : ∀ e, 0 ≤ y e)
    (hcons : ∀ v ∈ nodes U, v ≠ Node.src → v ≠ Node.snk → inF U y v = outF U y v) :
    ∀ m : ℕ, ∀ v ∈ nodes U, 2 * U.n + 3 - pot U v = m → (v = Node.snk ∨ 0 < outF U y v) →
      ∃ χ : arcs U → ℝ, (∀ e, χ e = 0 ∨ χ e = 1) ∧
        (∀ e, χ e ≠ 0 → 0 < y e ∧ pot U v ≤ pot U e.1.1) ∧
        (∀ u ∈ nodes U, inF U χ u - outF U χ u =
          (if u = Node.snk then 1 else 0) - (if u = v then 1 else 0)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hv hm hpos
  by_cases hvs : v = Node.snk
  · refine ⟨fun _ => 0, fun _ => Or.inl rfl, fun e h => absurd rfl h, ?_⟩
    intro u _
    subst hvs
    simp [inF, outF]
  have hp : 0 < outF U y v := hpos.resolve_left hvs
  obtain ⟨e, hev, hye⟩ := exists_pos_of_sum_pos U y _ hp
  have hf := arc_facts U hU e.1 e.2
  have hwpos : e.1.2 = Node.snk ∨ 0 < outF U y e.1.2 := by
    by_cases hws : e.1.2 = Node.snk
    · exact Or.inl hws
    · right
      rw [← hcons e.1.2 hf.2.2.2 hf.2.2.1 hws]
      have := le_inF U y hy0 e
      linarith
  rw [hev] at hf
  obtain ⟨χ', h01, hsupp, hcon⟩ :=
    ih (2 * U.n + 3 - pot U e.1.2) (by omega) e.1.2 hf.2.2.2 rfl hwpos
  have hχe : χ' e = 0 := by
    by_contra h
    have := (hsupp e h).2
    rw [hev] at this
    omega
  refine ⟨fun e' => χ' e' + if e' = e then 1 else 0, ?_, ?_, ?_⟩
  · intro e'
    by_cases h : e' = e
    · subst h; simp [hχe]
    · simp [h, h01 e']
  · intro e' hne
    by_cases h : e' = e
    · subst h; exact ⟨hye, by rw [hev]⟩
    · simp only [h, if_false, add_zero] at hne
      obtain ⟨h1, h2⟩ := hsupp e' hne
      exact ⟨h1, by omega⟩
  · intro u hu
    have hi : inF U (fun e' => χ' e' + if e' = e then 1 else 0) u =
        inF U χ' u + if u = e.1.2 then 1 else 0 := by
      simp only [inF, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite_eq']
      simp [eq_comm]
    have ho : outF U (fun e' => χ' e' + if e' = e then 1 else 0) u =
        outF U χ' u + if u = v then 1 else 0 := by
      simp only [outF, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite_eq']
      simp [hev, eq_comm]
    rw [hi, ho]
    have := hcon u hu
    split_ifs at this ⊢ <;> linarith

lemma demand_zero (v : Node) (h1 : v ≠ Node.src) (h2 : v ≠ Node.snk) : demand v = 0 := by
  cases v <;> simp_all [demand]

/-- the integral (0/1) points of the flow polytope -/
def I01 (U : ThermalUnit) : Set (arcs U → ℝ) := {χ | χ ∈ flowPoly U ∧ ∀ e, χ e = 0 ∨ χ e = 1}

lemma src_mem (U : ThermalUnit) : Node.src ∈ nodes U := by simp [nodes]

lemma decomp (U : ThermalUnit) (hU : U.Standing) : ∀ N : ℕ, ∀ y ∈ flowPoly U,
    (Finset.univ.filter (fun e => y e ≠ 0)).card = N → y ∈ convexHull ℝ (I01 U) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro y hy hN
  obtain ⟨hcons, hy0⟩ := hy
  have hc : ∀ u ∈ nodes U, inF U y u - outF U y u = demand u := hcons
  have hsrc_out : outF U y Node.src = 1 := by
    have := hc _ (src_mem U)
    rw [inF_src U hU] at this
    simp only [demand] at this
    linarith
  obtain ⟨χ, h01, hsupp, hχc⟩ := path_exists U hU y hy0
    (fun v hv h1 h2 => by have := hc v hv; rw [demand_zero v h1 h2] at this; linarith)
    _ Node.src (src_mem U) rfl (Or.inr (by rw [hsrc_out]; norm_num))
  have hχflow : ∀ u ∈ nodes U, inF U χ u - outF U χ u = demand u := by
    intro u hu
    rw [hχc u hu]
    cases u <;> simp [demand]
  have hχI : χ ∈ I01 U :=
    ⟨⟨hχflow, fun e => by rcases h01 e with h | h <;> simp [h]⟩, h01⟩
  have hχout : outF U χ Node.src = 1 := by
    have := hχflow _ (src_mem U)
    rw [inF_src U hU] at this
    simp only [demand] at this
    linarith
  obtain ⟨e1, -, he1⟩ := exists_pos_of_sum_pos U χ _ (by unfold outF at hχout; rw [hχout]; norm_num)
  have hS : (Finset.univ.filter (fun e : arcs U => χ e ≠ 0)).Nonempty := ⟨e1, by simp [he1.ne']⟩
  obtain ⟨e0, he0S, hmin⟩ := Finset.exists_min_image _ y hS
  have hχe0 : χ e0 ≠ 0 := (Finset.mem_filter.1 he0S).2
  have hχe0' : χ e0 = 1 := (h01 e0).resolve_left hχe0
  have hμ : 0 < y e0 := (hsupp e0 hχe0).1
  have hχ_le : ∀ e, y e0 * χ e ≤ y e := by
    intro e
    rcases h01 e with h | h
    · rw [h, mul_zero]; exact hy0 e
    · rw [h, mul_one]; exact hmin e (by simp [h])
  by_cases hμ1 : 1 ≤ y e0
  · have hc0 : ∀ e, 0 ≤ y e - χ e := by
      intro e
      rcases h01 e with h | h
      · rw [h, sub_zero]; exact hy0 e
      · have := hχ_le e; rw [h] at this ⊢; nlinarith
    have hcirc := circ_zero U hU (fun e => y e - χ e) hc0 (fun u hu => by
      have h1 := hc u hu
      have h2 := hχflow u hu
      have e1 : inF U (fun e => y e - χ e) u = inF U y u - inF U χ u := by
        simp [inF, Finset.sum_sub_distrib]
      have e2 : outF U (fun e => y e - χ e) u = outF U y u - outF U χ u := by
        simp [outF, Finset.sum_sub_distrib]
      rw [e1, e2]; linarith)
    have : y = χ := funext fun e => by linarith [hcirc e]
    rw [this]
    exact subset_convexHull ℝ _ hχI
  · push Not at hμ1
    have hne : (1 - y e0) ≠ 0 := by linarith
    set μ := y e0 with hμdef
    set y' : arcs U → ℝ := fun e => (1 - μ)⁻¹ * y e + (-(1 - μ)⁻¹ * μ) * χ e with hy'
    have hy'flow : y' ∈ flowPoly U := by
      refine ⟨?_, ?_⟩
      · intro u hu
        show inF U y' u - outF U y' u = demand u
        rw [hy', inF_lin, outF_lin]
        have hab : (1 - μ)⁻¹ + (-(1 - μ)⁻¹ * μ) = 1 := by field_simp; ring
        have h1 := hc u hu
        have h2 := hχflow u hu
        calc (1 - μ)⁻¹ * inF U y u + -(1 - μ)⁻¹ * μ * inF U χ u -
              ((1 - μ)⁻¹ * outF U y u + -(1 - μ)⁻¹ * μ * outF U χ u)
            = (1 - μ)⁻¹ * (inF U y u - outF U y u) +
              (-(1 - μ)⁻¹ * μ) * (inF U χ u - outF U χ u) := by ring
          _ = demand u := by rw [h1, h2, ← add_mul, hab, one_mul]
      · intro e
        have : y' e = (1 - μ)⁻¹ * (y e - μ * χ e) := by simp only [hy']; ring
        rw [this]
        exact mul_nonneg (inv_nonneg.2 (by linarith)) (by linarith [hχ_le e])
    have hsub : Finset.univ.filter (fun e => y' e ≠ 0) ⊂ Finset.univ.filter (fun e => y e ≠ 0) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨e0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hμ.ne', ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, hy', hχe0']
        field_simp
        ring
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        intro hye
        apply he
        have : χ e = 0 := by
          by_contra h
          have := (hsupp e h).1
          linarith
        simp [hy', hye, this]
    have hy'conv := ih _ (by rw [← hN]; exact Finset.card_lt_card hsub) y' hy'flow rfl
    have : y = μ • χ + (1 - μ) • y' := by
      funext e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy']
      field_simp
      ring
    rw [this]
    exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ hχI) hy'conv hμ.le (by linarith) (by ring)

lemma flowPoly_sub (U : ThermalUnit) (hU : U.Standing) : flowPoly U ⊆ convexHull ℝ (I01 U) :=
  fun y hy => decomp U hU _ y hy rfl

lemma pAt_smul (U : ThermalUnit) (c : ℝ) (p : Fin (U.n + 1) → ℝ) (t : ℕ) :
    pAt U (c • p) t = c * pAt U p t := by
  unfold pAt; split_ifs <;> simp

lemma pAt_zero (U : ThermalUnit) (t : ℕ) : pAt U 0 t = 0 := by
  unfold pAt; split_ifs <;> simp

lemma pAt_fin (U : ThermalUnit) (p : Fin (U.n + 1) → ℝ) (t : Fin (U.n + 1)) :
    pAt U p (t : ℕ) = p t := by
  simp [pAt, t.2]

lemma block_zero (U : ThermalUnit) (h k : ℕ) (z : ℝ) (hz : 0 ≤ z) : (0, 0, z) ∈ block U h k := by
  refine ⟨le_refl _, zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [pAt_zero, hz]

lemma block_zero_p (U : ThermalUnit) (h k : ℕ) (p : Fin (U.n + 1) → ℝ) (z : ℝ)
    (hb : (0, p, z) ∈ block U h k) : p = 0 ∧ 0 ≤ z := by
  obtain ⟨-, -, hh1, hh2, hmid, hk1, hk2, -, -, hout, hsum⟩ := hb
  simp only [mul_zero] at hh1 hh2 hk1 hk2 hsum hmid
  refine ⟨?_, by simpa using hsum⟩
  funext t
  by_cases ht : (t : ℕ) < h ∨ k < (t : ℕ)
  · exact hout t ht
  · push Not at ht
    rw [Pi.zero_apply, ← pAt_fin U p t]
    by_cases th : (t : ℕ) = h
    · rw [th]; linarith
    · by_cases tk : (t : ℕ) = k
      · rw [tk]; linarith
      · have := hmid t (by simp only [Finset.mem_Icc]; omega)
        linarith [this.1, this.2]

lemma block_scale (U : ThermalUnit) (h k : ℕ) (y : ℝ) (hy : 0 < y) (p : Fin (U.n + 1) → ℝ) (z : ℝ)
    (hb : (y, y • p, z) ∈ block U h k) : (1, p, z / y) ∈ block U h k := by
  obtain ⟨-, -, hh1, hh2, hmid, hk1, hk2, hru, hrd, hout, hsum⟩ := hb
  simp only [pAt_smul] at hh1 hh2 hmid hk1 hk2 hru hrd hsum
  refine ⟨zero_le_one, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; nlinarith
  · dsimp only; nlinarith
  · intro t ht; have := hmid t ht; dsimp only; constructor <;> nlinarith [this.1, this.2]
  · dsimp only; nlinarith
  · dsimp only; nlinarith
  · intro t ht; have := hru t ht; dsimp only; nlinarith
  · intro t ht; have := hrd t ht; dsimp only; nlinarith
  · intro t ht
    have := hout t ht
    simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left hy.ne'
  · dsimp only
    rw [le_div_iff₀ hy]
    simp only [mul_div_cancel_left₀ _ hy.ne', div_one, one_mul] at hsum ⊢
    rw [← Finset.mul_sum] at hsum
    linarith

/-- default dispatch: constant `l` on `T(h,k)` -/
def qdef (U : ThermalUnit) (h k : ℕ) : Fin (U.n + 1) → ℝ :=
  fun t => if h ≤ (t : ℕ) ∧ (t : ℕ) ≤ k then U.l else 0

lemma pAt_qdef (U : ThermalUnit) (h k t : ℕ) (hk : k ≤ U.n) (ht1 : h ≤ t) (ht2 : t ≤ k) :
    pAt U (qdef U h k) t = U.l := by
  simp [pAt, qdef, show t < U.n + 1 by omega, ht1, ht2]

lemma block_default (U : ThermalUnit) (hU : U.Standing) (a : onPairs U) (d : ℝ) (hd : 0 ≤ d) :
    (1, qdef U a.1.1 a.1.2, (∑ t ∈ Finset.Icc a.1.1 a.1.2, U.f U.l) + d) ∈ block U a.1.1 a.1.2 := by
  obtain ⟨h1, -, -, hl1, hl2, hl3, hl4, hd1, -, hd2, -, -⟩ := hU
  have ha := a.2
  simp only [onPairs, periods, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ha
  refine ⟨zero_le_one, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [pAt_qdef U _ _ _ (by omega) le_rfl (by omega)]; linarith
  · dsimp only; rw [pAt_qdef U _ _ _ (by omega) le_rfl (by omega)]; linarith
  · intro t ht
    simp only [Finset.mem_Icc] at ht
    dsimp only; rw [pAt_qdef U _ _ _ (by omega) (by omega) (by omega)]; constructor <;> linarith
  · dsimp only; rw [pAt_qdef U _ _ _ (by omega) (by omega) le_rfl]; linarith
  · dsimp only; rw [pAt_qdef U _ _ _ (by omega) (by omega) le_rfl]; linarith
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    dsimp only
    rw [pAt_qdef U _ _ _ (by omega) (by omega) (by omega), pAt_qdef U _ _ _ (by omega) (by omega) (by omega)]
    linarith
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    dsimp only
    rw [pAt_qdef U _ _ _ (by omega) (by omega) (by omega), pAt_qdef U _ _ _ (by omega) (by omega) (by omega)]
    linarith
  · intro t ht
    dsimp only
    simp only [qdef]
    rw [if_neg (by omega)]
  · dsimp only
    have : ∀ t ∈ Finset.Icc a.1.1 a.1.2, 1 * U.f (pAt U (qdef U a.1.1 a.1.2) t / 1) = U.f U.l := by
      intro t ht
      simp only [Finset.mem_Icc] at ht
      rw [pAt_qdef U _ _ _ (by omega) ht.1 ht.2]; simp
    rw [Finset.sum_congr rfl this]
    linarith

lemma out_src_one (U : ThermalUnit) (hU : U.Standing) (χ : arcs U → ℝ) (hχ : χ ∈ flowPoly U) :
    outF U χ Node.src = 1 := by
  have := hχ.1 _ (src_mem U)
  change inF U χ Node.src - outF U χ Node.src = demand Node.src at this
  rw [inF_src U hU] at this
  simp only [demand] at this
  linarith

lemma relax_sub (U : ThermalUnit) (hU : U.Standing) : relax U ⊆ convexHull ℝ (mixedInt U) := by
  intro x hx
  obtain ⟨hy, hblk⟩ := hx
  let q : onPairs U → Fin (U.n + 1) → ℝ := fun a =>
    if x.1 (onArc U a) = 0 then qdef U a.1.1 a.1.2 else (x.1 (onArc U a))⁻¹ • x.2.1 a
  let r : onPairs U → ℝ := fun a =>
    if x.1 (onArc U a) = 0 then ∑ t ∈ Finset.Icc a.1.1 a.1.2, U.f U.l else x.2.2 a / x.1 (onArc U a)
  let d : onPairs U → ℝ := fun a => if x.1 (onArc U a) = 0 then x.2.2 a else 0
  let L : (arcs U → ℝ) →ₗ[ℝ] Space U :=
    { toFun := fun χ => (χ, fun a => χ (onArc U a) • q a,
        fun a => χ (onArc U a) * r a + d a * outF U χ Node.src)
      map_add' := by
        intro χ1 χ2
        refine Prod.ext rfl (Prod.ext ?_ ?_)
        · funext a t; simp [add_mul]
        · funext a; simp [outF, Finset.sum_add_distrib]; ring
      map_smul' := by
        intro c χ
        refine Prod.ext rfl (Prod.ext ?_ ?_)
        · funext a t; simp [mul_assoc]
        · funext a
          show (c • χ) (onArc U a) * r a + d a * outF U (c • χ) Node.src =
            c * (χ (onArc U a) * r a + d a * outF U χ Node.src)
          have hs : outF U (c • χ) Node.src = c * outF U χ Node.src := by
            simp [outF, Finset.mul_sum]
          rw [hs, Pi.smul_apply, smul_eq_mul]
          ring }
  have hLy : L x.1 = x := by
    refine Prod.ext rfl (Prod.ext (funext fun a => ?_) (funext fun a => ?_))
    · show x.1 (onArc U a) • q a = x.2.1 a
      simp only [q]
      split_ifs with h0
      · have hb := hblk a
        rw [h0] at hb
        rw [h0, zero_smul]
        exact ((block_zero_p U _ _ _ _ hb).1).symm
      · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
    · show x.1 (onArc U a) * r a + d a * outF U x.1 Node.src = x.2.2 a
      rw [out_src_one U hU _ hy]
      simp only [r, d]
      split_ifs with h0
      · rw [h0]; ring
      · field_simp
        try simp
  have hLI : L '' I01 U ⊆ mixedInt U := by
    rintro _ ⟨χ, ⟨hχf, h01⟩, rfl⟩
    refine ⟨⟨hχf, fun a => ?_⟩, h01⟩
    show (χ (onArc U a), χ (onArc U a) • q a, χ (onArc U a) * r a + d a * outF U χ Node.src) ∈
      block U a.1.1 a.1.2
    rw [out_src_one U hU χ hχf, mul_one]
    have hd : 0 ≤ d a := by
      simp only [d]
      split_ifs with h0
      · have hb := hblk a
        rw [h0] at hb
        exact (block_zero_p U _ _ _ _ hb).2
      · exact le_refl 0
    rcases h01 (onArc U a) with h | h
    · rw [h, zero_smul, zero_mul, zero_add]
      exact block_zero U _ _ _ hd
    · rw [h, one_smul, one_mul]
      simp only [q, r, d] at hd ⊢
      split_ifs with h0
      · rw [if_pos h0] at hd
        exact block_default U hU a _ hd
      · have hpos : 0 < x.1 (onArc U a) := lt_of_le_of_ne (hy.2 _) (Ne.symm h0)
        rw [add_zero]
        apply block_scale U _ _ _ hpos
        rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
        exact hblk a
  have hmem : x ∈ L '' convexHull ℝ (I01 U) := ⟨x.1, flowPoly_sub U hU hy, hLy⟩
  rw [LinearMap.image_convexHull] at hmem
  exact convexHull_mono hLI hmem

lemma persp (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (a b y1 y2 p1 p2 : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2)
    (hp1 : y1 = 0 → p1 = 0) (hp2 : y2 = 0 → p2 = 0) :
    (a * y1 + b * y2) * f ((a * p1 + b * p2) / (a * y1 + b * y2)) ≤
      a * (y1 * f (p1 / y1)) + b * (y2 * f (p2 / y2)) := by
  have h1 : 0 ≤ a * y1 := mul_nonneg ha hy1
  have h2 : 0 ≤ b * y2 := mul_nonneg hb hy2
  rcases (add_nonneg h1 h2).eq_or_lt with hY | hY
  · have e1 : a * y1 = 0 := by linarith
    have e2 : b * y2 = 0 := by linarith
    rw [← hY, zero_mul, ← mul_assoc, ← mul_assoc, e1, e2]
    simp
  · set Y := a * y1 + b * y2 with hYdef
    have hYne : Y ≠ 0 := hY.ne'
    have k1 : a * p1 / Y = (a * y1 / Y) * (p1 / y1) := by
      by_cases h : y1 = 0
      · simp [h, hp1 h]
      · field_simp
    have k2 : b * p2 / Y = (b * y2 / Y) * (p2 / y2) := by
      by_cases h : y2 = 0
      · simp [h, hp2 h]
      · field_simp
    have hw : a * y1 / Y + b * y2 / Y = 1 := by rw [← add_div]; exact div_self hYne
    have hc := hf.2 (Set.mem_univ (p1 / y1)) (Set.mem_univ (p2 / y2))
      (div_nonneg h1 hY.le) (div_nonneg h2 hY.le) hw
    simp only [smul_eq_mul] at hc
    have harg : (a * p1 + b * p2) / Y = a * y1 / Y * (p1 / y1) + b * y2 / Y * (p2 / y2) := by
      rw [add_div, k1, k2]
    rw [harg]
    calc Y * f (a * y1 / Y * (p1 / y1) + b * y2 / Y * (p2 / y2))
        ≤ Y * (a * y1 / Y * f (p1 / y1) + b * y2 / Y * f (p2 / y2)) :=
          mul_le_mul_of_nonneg_left hc hY.le
      _ = a * (y1 * f (p1 / y1)) + b * (y2 * f (p2 / y2)) := by
          field_simp

lemma pAt_comb (U : ThermalUnit) (a b : ℝ) (p1 p2 : Fin (U.n + 1) → ℝ) (t : ℕ) :
    pAt U (a • p1 + b • p2) t = a * pAt U p1 t + b * pAt U p2 t := by
  unfold pAt; split_ifs <;> simp

lemma block_convex (U : ThermalUnit) (hU : U.Standing) (h k : ℕ) : Convex ℝ (block U h k) := by
  have hfc : ConvexOn ℝ Set.univ U.f := hU.2.2.2.2.2.2.2.2.2.2.2
  rintro ⟨y1, p1, z1⟩ hq1 ⟨y2, p2, z2⟩ hq2 a b ha hb hab
  have hz1 : y1 = 0 → p1 = 0 := fun h0 => (block_zero_p U h k p1 z1 (h0 ▸ hq1)).1
  have hz2 : y2 = 0 → p2 = 0 := fun h0 => (block_zero_p U h k p2 z2 (h0 ▸ hq2)).1
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hq1
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hq2
  dsimp only at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> try simp only [pAt_comb]
  · positivity
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left a2 ha, mul_le_mul_of_nonneg_left b2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left a3 ha, mul_le_mul_of_nonneg_left b3 hb]
  · intro t ht
    obtain ⟨c1, c2⟩ := a4 t ht
    obtain ⟨d1, d2⟩ := b4 t ht
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left c1 ha, mul_le_mul_of_nonneg_left d1 hb]
    · nlinarith [mul_le_mul_of_nonneg_left c2 ha, mul_le_mul_of_nonneg_left d2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left a5 ha, mul_le_mul_of_nonneg_left b5 hb]
  · nlinarith [mul_le_mul_of_nonneg_left a6 ha, mul_le_mul_of_nonneg_left b6 hb]
  · intro t ht
    nlinarith [mul_le_mul_of_nonneg_left (a7 t ht) ha, mul_le_mul_of_nonneg_left (b7 t ht) hb]
  · intro t ht
    nlinarith [mul_le_mul_of_nonneg_left (a8 t ht) ha, mul_le_mul_of_nonneg_left (b8 t ht) hb]
  · intro t ht
    simp [a9 t ht, b9 t ht]
  · calc ∑ t ∈ Finset.Icc h k, (a * y1 + b * y2) *
          U.f ((a * pAt U p1 t + b * pAt U p2 t) / (a * y1 + b * y2))
        ≤ ∑ t ∈ Finset.Icc h k, (a * (y1 * U.f (pAt U p1 t / y1)) +
            b * (y2 * U.f (pAt U p2 t / y2))) := by
          apply Finset.sum_le_sum
          intro t _
          exact persp U.f hfc a b y1 y2 _ _ ha hb a0 b0
            (fun h0 => by rw [hz1 h0, pAt_zero]) (fun h0 => by rw [hz2 h0, pAt_zero])
      _ = a * ∑ t ∈ Finset.Icc h k, y1 * U.f (pAt U p1 t / y1) +
            b * ∑ t ∈ Finset.Icc h k, y2 * U.f (pAt U p2 t / y2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ a * z1 + b * z2 := by
          nlinarith [mul_le_mul_of_nonneg_left a10 ha, mul_le_mul_of_nonneg_left b10 hb]

lemma relax_convex (U : ThermalUnit) (hU : U.Standing) : Convex ℝ (relax U) := by
  rintro x ⟨hxf, hxb⟩ x' ⟨hxf', hxb'⟩ a b ha hb hab
  refine ⟨⟨?_, ?_⟩, fun c => ?_⟩
  · intro u hu
    show inF U (fun e => a * x.1 e + b * x'.1 e) u - outF U (fun e => a * x.1 e + b * x'.1 e) u =
      demand u
    rw [inF_lin, outF_lin]
    have h1 : inF U x.1 u - outF U x.1 u = demand u := hxf.1 u hu
    have h2 : inF U x'.1 u - outF U x'.1 u = demand u := hxf'.1 u hu
    calc a * inF U x.1 u + b * inF U x'.1 u - (a * outF U x.1 u + b * outF U x'.1 u)
        = a * (inF U x.1 u - outF U x.1 u) + b * (inF U x'.1 u - outF U x'.1 u) := by ring
      _ = demand u := by rw [h1, h2, ← add_mul, hab, one_mul]
  · intro e
    show 0 ≤ a * x.1 e + b * x'.1 e
    exact add_nonneg (mul_nonneg ha (hxf.2 e)) (mul_nonneg hb (hxf'.2 e))
  · have := block_convex U hU _ _ (hxb c) (hxb' c) ha hb hab
    convert this using 1
    simp

lemma cont_pAt (U : ThermalUnit) (t : ℕ) : Continuous (fun p : Fin (U.n + 1) → ℝ => pAt U p t) := by
  by_cases ht : t < U.n + 1
  · simp only [pAt, ht, dif_pos]; exact continuous_apply _
  · simp only [pAt, ht, dif_neg, not_false_eq_true]; exact continuous_const

/-- the linear part of a dispatch block -/
def Kset (U : ThermalUnit) (h k : ℕ) : Set (ℝ × (Fin (U.n + 1) → ℝ) × ℝ) :=
  {q |
    0 ≤ q.1 ∧ q.1 ≤ 1 ∧
    U.l * q.1 ≤ pAt U q.2.1 h ∧ pAt U q.2.1 h ≤ U.lbar * q.1 ∧
    (∀ t ∈ Finset.Icc (h + 1) (k - 1), U.l * q.1 ≤ pAt U q.2.1 t ∧ pAt U q.2.1 t ≤ U.u * q.1) ∧
    U.l * q.1 ≤ pAt U q.2.1 k ∧ pAt U q.2.1 k ≤ U.ubar * q.1 ∧
    (∀ t ∈ Finset.Ico h k, pAt U q.2.1 (t + 1) ≤ pAt U q.2.1 t + q.1 * U.Δup) ∧
    (∀ t ∈ Finset.Ico h k, pAt U q.2.1 t ≤ pAt U q.2.1 (t + 1) + q.1 * U.Δdn) ∧
    (∀ t : Fin (U.n + 1), ((t : ℕ) < h ∨ k < (t : ℕ)) → q.2.1 t = 0)}

/-- slack of the perspective epigraph -/
noncomputable def Gfun (U : ThermalUnit) (h k : ℕ) (q : ℝ × (Fin (U.n + 1) → ℝ) × ℝ) : ℝ :=
  q.2.2 - ∑ t ∈ Finset.Icc h k, q.1 * U.f (pAt U q.2.1 t / q.1)

lemma block_eq (U : ThermalUnit) (h k : ℕ) :
    block U h k = Kset U h k ∩ Gfun U h k ⁻¹' Set.Ici 0 := by
  ext q
  simp only [block, Kset, Gfun, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_Ici, sub_nonneg, and_assoc]

lemma Kset_closed (U : ThermalUnit) (h k : ℕ) : IsClosed (Kset U h k) := by
  have c1 : Continuous fun q : ℝ × (Fin (U.n + 1) → ℝ) × ℝ => q.1 := continuous_fst
  have cp : ∀ t : ℕ, Continuous fun q : ℝ × (Fin (U.n + 1) → ℝ) × ℝ => pAt U q.2.1 t :=
    fun t => (cont_pAt U t).comp (continuous_fst.comp continuous_snd)
  have cz : ∀ t : Fin (U.n + 1), Continuous fun q : ℝ × (Fin (U.n + 1) → ℝ) × ℝ => q.2.1 t :=
    fun t => (continuous_apply t).comp (continuous_fst.comp continuous_snd)
  simp only [Kset, Set.setOf_and, Set.setOf_forall]
  repeat' first
    | apply IsClosed.inter
    | (apply isClosed_iInter; intro _)
    | apply isClosed_le
    | apply isClosed_eq
    | exact continuous_const
    | exact c1
    | exact cp _
    | exact cz _
    | apply Continuous.add
    | apply Continuous.mul

lemma Kset_bound (U : ThermalUnit) (hU : U.Standing) (h k : ℕ) (q : ℝ × (Fin (U.n + 1) → ℝ) × ℝ)
    (hq : q ∈ Kset U h k) (t : ℕ) (ht : t ∈ Finset.Icc h k) :
    U.l * q.1 ≤ pAt U q.2.1 t ∧ pAt U q.2.1 t ≤ U.u * q.1 := by
  obtain ⟨-, -, -, -, hl1, hl2, hl3, hl4, -, -, -, -⟩ := hU
  obtain ⟨h0, -, hh1, hh2, hmid, hk1, hk2, -, -, -⟩ := hq
  simp only [Finset.mem_Icc] at ht
  by_cases th : t = h
  · subst th; exact ⟨hh1, by nlinarith⟩
  · by_cases tk : t = k
    · subst tk; exact ⟨hk1, by nlinarith⟩
    · exact hmid t (by simp only [Finset.mem_Icc]; omega)

lemma block_closed (U : ThermalUnit) (hU : U.Standing) (h k : ℕ) : IsClosed (block U h k) := by
  have hfcv : ConvexOn ℝ Set.univ U.f := hU.2.2.2.2.2.2.2.2.2.2.2
  have hfc : Continuous U.f := continuousOn_univ.1 (hfcv.continuousOn isOpen_univ)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := U.l) (b := U.u)).exists_bound_of_continuousOn
    hfc.continuousOn
  have cp : ∀ t : ℕ, Continuous fun q : ℝ × (Fin (U.n + 1) → ℝ) × ℝ => pAt U q.2.1 t :=
    fun t => (cont_pAt U t).comp (continuous_fst.comp continuous_snd)
  have gbound : ∀ q ∈ Kset U h k, ∀ t ∈ Finset.Icc h k,
      ‖q.1 * U.f (pAt U q.2.1 t / q.1)‖ ≤ M * q.1 := by
    intro q hq t ht
    have h0 : 0 ≤ q.1 := hq.1
    rcases h0.eq_or_lt with hq0 | hq0
    · rw [← hq0]; simp
    · obtain ⟨b1, b2⟩ := Kset_bound U hU h k q hq t ht
      have hmem : pAt U q.2.1 t / q.1 ∈ Set.Icc U.l U.u :=
        ⟨by rw [le_div_iff₀ hq0]; linarith, by rw [div_le_iff₀ hq0]; linarith⟩
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hq0, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _ hmem) hq0.le
  have hg : ∀ t ∈ Finset.Icc h k, ContinuousOn
      (fun q : ℝ × (Fin (U.n + 1) → ℝ) × ℝ => q.1 * U.f (pAt U q.2.1 t / q.1)) (Kset U h k) := by
    intro t ht q hq
    by_cases hq0 : q.1 = 0
    · rw [ContinuousWithinAt, show q.1 * U.f (pAt U q.2.1 t / q.1) = 0 by rw [hq0, zero_mul]]
      apply squeeze_zero_norm' (a := fun q' : ℝ × (Fin (U.n + 1) → ℝ) × ℝ => M * q'.1)
      · filter_upwards [self_mem_nhdsWithin] with q' hq' using gbound q' hq' t ht
      · have : Filter.Tendsto (fun q' : ℝ × (Fin (U.n + 1) → ℝ) × ℝ => M * q'.1) (nhds q)
            (nhds (M * q.1)) := (continuous_const.mul continuous_fst).tendsto q
        rw [hq0, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
    · apply ContinuousAt.continuousWithinAt
      exact continuous_fst.continuousAt.mul
        (hfc.continuousAt.comp ((cp t).continuousAt.div continuous_fst.continuousAt hq0))
  have hG : ContinuousOn (Gfun U h k) (Kset U h k) :=
    (continuous_snd.comp continuous_snd).continuousOn.sub (continuousOn_finsetSum _ hg)
  rw [block_eq]
  exact hG.preimage_isClosed_of_isClosed (Kset_closed U h k) isClosed_Ici

lemma flowPoly_closed (U : ThermalUnit) : IsClosed (flowPoly U) := by
  have : flowPoly U = (⋂ v ∈ nodes U, {y | inF U y v - outF U y v = demand v}) ∩
      ⋂ e, {y : arcs U → ℝ | 0 ≤ y e} := by
    ext y
    simp only [flowPoly, FlowCons, inF, outF, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  refine IsClosed.inter (isClosed_biInter fun v _ => isClosed_eq ?_ continuous_const)
    (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e))
  unfold inF outF
  exact (continuous_finsetSum _ fun e _ => continuous_apply e).sub
    (continuous_finsetSum _ fun e _ => continuous_apply e)

lemma relax_closed (U : ThermalUnit) (hU : U.Standing) : IsClosed (relax U) := by
  have : relax U = (Prod.fst ⁻¹' flowPoly U) ∩ ⋂ a : onPairs U,
      (fun x : Space U => (x.1 (onArc U a), x.2.1 a, x.2.2 a)) ⁻¹' block U a.1.1 a.1.2 := by
    ext x
    simp only [relax, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact ((flowPoly_closed U).preimage continuous_fst).inter
    (isClosed_iInter fun a => (block_closed U hU _ _).preimage (by fun_prop))

end UCConvexHull.OneUC.Pf

open UCConvexHull.OneUC in
theorem solution (U : ThermalUnit) (hU : U.Standing) :
    relax U = closure (convexHull ℝ (mixedInt U)) := by
  apply Set.Subset.antisymm
  · exact (Pf.relax_sub U hU).trans subset_closure
  · exact closure_minimal (convexHull_min (fun x hx => hx.1) (Pf.relax_convex U hU))
      (Pf.relax_closed U hU)
