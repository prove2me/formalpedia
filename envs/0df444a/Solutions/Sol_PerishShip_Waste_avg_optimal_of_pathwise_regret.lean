-- Prove2me | solution 1 for PerishShip.Waste.avg_optimal_of_pathwise_regret
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:12:57.863512+00:00
-- url     : https://prove2.me/submissions/6069e91b-58bd-4029-af4d-4b5341a0234b

import Mathlib
import Definitions.Def_PerishShip_Waste_AverageMDP

open Filter Topology

namespace PerishShipAvgPathAux

open PerishShip.Waste

variable {S A Ω : Type} [Countable S] [Countable Ω]

/-- Sample path of a Markov policy driven by a shock sequence. -/
def traj (step : S → A → Ω → S) (σ : MarkovPolicy S A) (s : S) (w : ℕ → Ω) : ℕ → S
  | 0 => s
  | t + 1 => step (traj step σ s w t) (σ t (traj step σ s w t)) (w t)

noncomputable def pathCost (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s : S) (w : ℕ → Ω) (T : ℕ) : ENNReal :=
  ∑ t ∈ Finset.range T, cost (traj step σ s w t) (σ t (traj step σ s w t)) (w t)

def shiftP (σ : MarkovPolicy S A) : MarkovPolicy S A := fun t => σ (t + 1)

def consSeq (a : Ω) (w : ℕ → Ω) : ℕ → Ω
  | 0 => a
  | n + 1 => w n

/-- Law of a shock sequence whose first `T` entries are i.i.d. -/
noncomputable def seqLaw (demand : PMF Ω) (ω₀ : Ω) : ℕ → PMF (ℕ → Ω)
  | 0 => PMF.pure (fun _ => ω₀)
  | T + 1 => demand.bind (fun a => (seqLaw demand ω₀ T).map (consSeq a))

lemma traj_cons (step : S → A → Ω → S) (σ : MarkovPolicy S A) (s : S) (a : Ω)
    (w : ℕ → Ω) (t : ℕ) :
    traj step σ s (consSeq a w) (t + 1) = traj step (shiftP σ) (step s (σ 0 s) a) w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show step (traj step σ s (consSeq a w) (t + 1)) (σ (t + 1) (traj step σ s (consSeq a w) (t + 1)))
        (w t) = _
    rw [ih]; rfl

lemma pathCost_cons (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s : S) (a : Ω) (w : ℕ → Ω) (T : ℕ) :
    pathCost step cost σ s (consSeq a w) (T + 1) =
      pathCost step cost (shiftP σ) (step s (σ 0 s) a) w T + cost s (σ 0 s) a := by
  unfold pathCost
  rw [Finset.sum_range_succ']
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [traj_cons]; rfl

lemma tsum_bind_mul {α β : Type} (p : PMF α) (f : α → PMF β) (g : β → ENNReal) :
    ∑' b, (p.bind f) b * g b = ∑' a, p a * ∑' b, f a b * g b := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun a => ?_)
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun b => ?_)
  ring

lemma tsum_pure_mul {α : Type} (a : α) (g : α → ENNReal) :
    ∑' b, (PMF.pure a) b * g b = g a := by
  classical
  simp_rw [PMF.pure_apply]
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [hb]

lemma tsum_map_mul {α β : Type} (p : PMF α) (f : α → β) (g : β → ENNReal) :
    ∑' b, (p.map f) b * g b = ∑' a, p a * g (f a) := by
  rw [← PMF.bind_pure_comp, tsum_bind_mul]
  refine tsum_congr (fun a => ?_)
  rw [Function.comp_apply, tsum_pure_mul]

lemma law_succ_first (demand : PMF Ω) (step : S → A → Ω → S) (σ : MarkovPolicy S A)
    (s : S) (t : ℕ) :
    controlledStateLaw demand step σ s (t + 1) =
      demand.bind (fun a => controlledStateLaw demand step (shiftP σ) (step s (σ 0 s) a) t) := by
  induction t with
  | zero =>
    show (PMF.pure s).bind (fun s => demand.map (step s (σ 0 s))) = _
    rw [PMF.pure_bind]
    rw [← PMF.bind_pure_comp]
    rfl
  | succ t ih =>
    show (controlledStateLaw demand step σ s (t + 1)).bind
      (fun s' => demand.map (step s' (σ (t + 1) s'))) = _
    rw [ih, PMF.bind_bind]
    rfl

lemma expCost_succ (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s : S) (t : ℕ) :
    controlledExpectedCost demand step cost σ s (t + 1) =
      ∑' a, demand a * controlledExpectedCost demand step cost (shiftP σ) (step s (σ 0 s) a) t := by
  unfold controlledExpectedCost
  rw [law_succ_first, tsum_bind_mul]
  rfl

lemma expCost_zero (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s : S) :
    controlledExpectedCost demand step cost σ s 0 = ∑' a, demand a * cost s (σ 0 s) a := by
  unfold controlledExpectedCost
  show ∑' s', (PMF.pure s) s' * _ = _
  rw [tsum_pure_mul]

/-- Finite-horizon expected cost. -/
noncomputable def J (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s : S) (T : ℕ) : ENNReal :=
  ∑ t ∈ Finset.range T, controlledExpectedCost demand step cost σ s t

lemma J_succ (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s : S) (T : ℕ) :
    J demand step cost σ s (T + 1) =
      ∑' a, demand a * (J demand step cost (shiftP σ) (step s (σ 0 s) a) T + cost s (σ 0 s) a) := by
  unfold J
  rw [Finset.sum_range_succ']
  simp_rw [expCost_succ, expCost_zero]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
  refine tsum_congr (fun a => ?_)
  rw [mul_add, Finset.mul_sum]

lemma J_eq_path (demand : PMF Ω) (ω₀ : Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (T : ℕ) : ∀ (σ : MarkovPolicy S A) (s : S),
    J demand step cost σ s T = ∑' w, seqLaw demand ω₀ T w * pathCost step cost σ s w T := by
  induction T with
  | zero =>
    intro σ s
    simp [J, pathCost]
  | succ T ih =>
    intro σ s
    rw [J_succ]
    show _ = ∑' w, (demand.bind (fun a => (seqLaw demand ω₀ T).map (consSeq a))) w * _
    rw [tsum_bind_mul]
    refine tsum_congr (fun a => ?_)
    congr 1
    rw [tsum_map_mul]
    simp_rw [pathCost_cons, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ih]

lemma law_add (demand : PMF Ω) (step : S → A → Ω → S) (f : S → A) (s₀ : S) (m t : ℕ) :
    controlledStateLaw demand step (fun _ => f) s₀ (m + t) =
      (controlledStateLaw demand step (fun _ => f) s₀ m).bind
        (fun x => controlledStateLaw demand step (fun _ => f) x t) := by
  induction t with
  | zero =>
    show _ = (controlledStateLaw demand step (fun _ => f) s₀ m).bind PMF.pure
    rw [PMF.bind_pure]; rfl
  | succ t ih =>
    show (controlledStateLaw demand step (fun _ => f) s₀ (m + t)).bind
      (fun s' => demand.map (step s' (f s'))) = _
    rw [ih, PMF.bind_bind]
    rfl

lemma law_support (demand : PMF Ω) (step : S → A → Ω → S) (f : S → A) (F : Set S)
    (hF : ∀ s ∈ F, ∀ ω, step s (f s) ω ∈ F) (s₀ : S) (hs₀ : s₀ ∈ F) (m : ℕ) (x : S)
    (hx : controlledStateLaw demand step (fun _ => f) s₀ m x ≠ 0) : x ∈ F := by
  induction m generalizing x with
  | zero =>
    have : x ∈ (PMF.pure s₀).support := hx
    rw [PMF.support_pure] at this
    rw [Set.mem_singleton_iff.mp this]; exact hs₀
  | succ m ih =>
    have : x ∈ ((controlledStateLaw demand step (fun _ => f) s₀ m).bind
      (fun s' => demand.map (step s' (f s')))).support := hx
    rw [PMF.mem_support_bind_iff] at this
    obtain ⟨y, hy, hxy⟩ := this
    rw [PMF.mem_support_map_iff] at hxy
    obtain ⟨a, _, rfl⟩ := hxy
    exact hF y (ih y hy) a

end PerishShipAvgPathAux

open PerishShip.Waste PerishShipAvgPathAux in
theorem solution {S A Ω : Type} [Countable S] [Countable Ω]
    (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (f : S → A) (σ : MarkovPolicy S A) (s₀ : S) (F : Set S) (B C : ENNReal)
    (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hs₀ : s₀ ∈ F)
    (hF : ∀ s ∈ F, ∀ ω, step s (f s) ω ∈ F)
    (hcost : ∀ s ∈ F, ∀ ω, cost s (f s) ω ≤ B)
    (hpath : ∀ (w : ℕ → Ω) (x : S), x ∈ F → ∀ (u v : ℕ → S), u 0 = x → v 0 = s₀ →
      (∀ t, u (t + 1) = step (u t) (f (u t)) (w t)) →
      (∀ t, v (t + 1) = step (v t) (σ t (v t)) (w t)) →
      ∀ T, ∑ t ∈ Finset.range T, cost (u t) (f (u t)) (w t) ≤
        ∑ t ∈ Finset.range T, cost (v t) (σ t (v t)) (w t) + C) :
    controlledAvgUpper demand step cost (fun _ => f) s₀ ≤
      controlledAvgLower demand step cost σ s₀ := by
  classical
  -- a default shock
  obtain ⟨ω₀, -⟩ := demand.support_nonempty
  set Pf : MarkovPolicy S A := fun _ => f with hPf
  have hshift : shiftP Pf = Pf := rfl
  -- (1) expected regret bound from any state of `F`
  have hreg : ∀ x ∈ F, ∀ T, J demand step cost Pf x T ≤ J demand step cost σ s₀ T + C := by
    intro x hx T
    rw [J_eq_path demand ω₀, J_eq_path demand ω₀]
    calc ∑' w, seqLaw demand ω₀ T w * pathCost step cost Pf x w T
        ≤ ∑' w, seqLaw demand ω₀ T w * (pathCost step cost σ s₀ w T + C) := by
          refine ENNReal.tsum_le_tsum (fun w => ?_)
          gcongr
          exact hpath w x hx (traj step Pf x w) (traj step σ s₀ w) rfl rfl (fun t => rfl)
            (fun t => rfl) T
      _ = _ := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  -- (2) block decomposition
  have hblock : ∀ m T₀, ∑ t ∈ Finset.range T₀, controlledExpectedCost demand step cost Pf s₀ (m + t)
      ≤ J demand step cost σ s₀ T₀ + C := by
    intro m T₀
    have : ∀ t, controlledExpectedCost demand step cost Pf s₀ (m + t) =
        ∑' x, controlledStateLaw demand step Pf s₀ m x *
          controlledExpectedCost demand step cost Pf x t := by
      intro t
      unfold controlledExpectedCost
      rw [law_add, tsum_bind_mul]
    simp_rw [this]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [← Finset.mul_sum]
    calc ∑' x, controlledStateLaw demand step Pf s₀ m x *
          ∑ t ∈ Finset.range T₀, controlledExpectedCost demand step cost Pf x t
        ≤ ∑' x, controlledStateLaw demand step Pf s₀ m x * (J demand step cost σ s₀ T₀ + C) := by
          refine ENNReal.tsum_le_tsum (fun x => ?_)
          by_cases h0 : controlledStateLaw demand step Pf s₀ m x = 0
          · simp [h0]
          · gcongr
            exact hreg x (law_support demand step f F hF s₀ hs₀ m x h0) T₀
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  -- (3) uniform bound on period costs
  have hper : ∀ t, controlledExpectedCost demand step cost Pf s₀ t ≤ B := by
    intro t
    unfold controlledExpectedCost
    calc ∑' x, controlledStateLaw demand step Pf s₀ t x * ∑' ω, demand ω * cost x (Pf t x) ω
        ≤ ∑' x, controlledStateLaw demand step Pf s₀ t x * B := by
          refine ENNReal.tsum_le_tsum (fun x => ?_)
          by_cases h0 : controlledStateLaw demand step Pf s₀ t x = 0
          · simp [h0]
          · gcongr
            have hx := law_support demand step f F hF s₀ hs₀ t x h0
            calc ∑' ω, demand ω * cost x (Pf t x) ω ≤ ∑' ω, demand ω * B := by
                  refine ENNReal.tsum_le_tsum (fun ω => ?_)
                  gcongr
                  exact hcost x hx ω
              _ = B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ = B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  -- (4) total over `n` blocks plus remainder
  have hsum : ∀ T₀, 0 < T₀ → ∀ T, ∑ t ∈ Finset.range T, controlledExpectedCost demand step cost Pf s₀ t ≤
      (T / T₀ : ℕ) * (J demand step cost σ s₀ T₀ + C) + T₀ * B := by
    intro T₀ hT₀pos T
    have hn : ∀ n, ∑ t ∈ Finset.range (n * T₀), controlledExpectedCost demand step cost Pf s₀ t ≤
        n * (J demand step cost σ s₀ T₀ + C) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.succ_mul, Finset.sum_range_add]
        push_cast
        rw [add_mul, one_mul]
        exact add_le_add ih (hblock _ _)
    have hT₀ : T₀ ≠ 0 := hT₀pos.ne'
    · have hdecomp : T = (T / T₀) * T₀ + T % T₀ := (Nat.div_add_mod' T T₀).symm
      conv_lhs => rw [hdecomp, Finset.sum_range_add]
      refine add_le_add (hn _) ?_
      calc ∑ x ∈ Finset.range (T % T₀), controlledExpectedCost demand step cost Pf s₀ (T / T₀ * T₀ + x)
          ≤ ∑ x ∈ Finset.range (T % T₀), B := Finset.sum_le_sum (fun x _ => hper _)
        _ = (T % T₀ : ℕ) * B := by simp
        _ ≤ T₀ * B := by
            gcongr
            exact_mod_cast (Nat.mod_lt _ (Nat.pos_of_ne_zero hT₀)).le
  -- (5) analysis
  have key : ∀ T₀, 0 < T₀ → controlledAvgUpper demand step cost Pf s₀ ≤
      controlledCesaro demand step cost σ s₀ T₀ + C / T₀ := by
    intro T₀ hT₀
    set X := J demand step cost σ s₀ T₀ + C with hX
    have hlim : Tendsto (fun T : ℕ => X / T₀ + ((T₀ : ENNReal) * B) * (T : ENNReal)⁻¹) atTop
        (𝓝 (X / T₀)) := by
      have h0 : Tendsto (fun T : ℕ => ((T₀ : ENNReal) * B) * (T : ENNReal)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top T₀) hB))
        simpa using this
      simpa using (tendsto_const_nhds (x := X / T₀)).add h0
    have hle : ∀ᶠ T : ℕ in atTop, controlledCesaro demand step cost Pf s₀ T ≤
        X / T₀ + ((T₀ : ENNReal) * B) * (T : ENNReal)⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with T hT
      have hT0 : (T : ENNReal) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hT)
      have hTt : (T : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top T
      unfold controlledCesaro
      calc (∑ t ∈ Finset.range T, controlledExpectedCost demand step cost Pf s₀ t) / T
          ≤ (((T / T₀ : ℕ) : ENNReal) * X + T₀ * B) / T := by
            gcongr; exact hsum T₀ hT₀ T
        _ = ((T / T₀ : ℕ) : ENNReal) * X / T + ((T₀ : ENNReal) * B) * (T : ENNReal)⁻¹ := by
            rw [ENNReal.add_div, div_eq_mul_inv ((T₀ : ENNReal) * B)]
        _ ≤ X / T₀ + ((T₀ : ENNReal) * B) * (T : ENNReal)⁻¹ := by
            refine add_le_add ?_ le_rfl
            rw [ENNReal.div_le_iff hT0 hTt]
            have hn : ((T / T₀ : ℕ) : ENNReal) ≤ (T : ENNReal) / T₀ := by
              rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hT₀.ne'))
                (Or.inl (ENNReal.natCast_ne_top T₀))]
              exact_mod_cast Nat.div_mul_le_self T T₀
            calc ((T / T₀ : ℕ) : ENNReal) * X = X * ((T / T₀ : ℕ) : ENNReal) := mul_comm _ _
              _ ≤ X * ((T : ENNReal) / T₀) := by gcongr
              _ = X / T₀ * T := by
                  rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    calc controlledAvgUpper demand step cost Pf s₀
        = limsup (controlledCesaro demand step cost Pf s₀) atTop := rfl
      _ ≤ limsup (fun T : ℕ => X / T₀ + ((T₀ : ENNReal) * B) * (T : ENNReal)⁻¹) atTop :=
          Filter.limsup_le_limsup hle
      _ = X / T₀ := hlim.limsup_eq
      _ = controlledCesaro demand step cost σ s₀ T₀ + C / T₀ := by
          rw [hX, ENNReal.add_div]; rfl
  have hCt : Tendsto (fun T₀ : ℕ => C / T₀) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
    simpa [div_eq_mul_inv] using this
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hev : ∀ᶠ T₀ : ℕ in atTop, controlledAvgUpper demand step cost Pf s₀ - ε ≤
      controlledCesaro demand step cost σ s₀ T₀ := by
    have h1 := (tendsto_order.1 hCt).2 ε (by exact_mod_cast hε)
    filter_upwards [h1, eventually_ge_atTop 1] with T₀ h1 h2
    rw [tsub_le_iff_right]
    exact (key T₀ h2).trans (by gcongr)
  have := Filter.le_liminf_of_le (by isBoundedDefault) hev
  exact tsub_le_iff_right.1 this
