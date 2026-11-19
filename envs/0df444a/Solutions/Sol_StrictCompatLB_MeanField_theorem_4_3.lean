-- Prove2me | solution 1 for StrictCompatLB.MeanField.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:54:10.800873+00:00
-- url     : https://prove2.me/submissions/8d14bfd0-a1c0-4e13-be38-82c1abe7c721

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Theorems.Thm_StrictCompatLB_MeanField_perturbed_meanfield_lln
import Theorems.Thm_StrictCompatLB_MeanField_proposition_4_5

set_option autoImplicit false

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace SC66L

open StrictCompatLB.MeanField

/-- Empirical distribution of `z` over a finite set `S` of servers. -/
noncomputable def emp {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℕ) (i : ℕ) : ℝ :=
  ((S.filter (fun v => z v = i)).card : ℝ) / (S.card : ℝ)

lemma emp_inX {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) (z : Fin N → ℕ) :
    InX (emp S z) := by
  refine ⟨fun i => by unfold emp; positivity, ?_⟩
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hzero : ∀ i ∉ range (S.sup z + 1), emp S z i = 0 := by
    intro i hi
    simp only [mem_range, not_lt] at hi
    have : S.filter (fun v => z v = i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv hvi
      have := Finset.le_sup (f := z) hv
      omega
    simp [emp, this]
  have hsum : ∑ i ∈ range (S.sup z + 1), emp S z i = 1 := by
    unfold emp
    rw [← Finset.sum_div]
    have hcard : S.card = ∑ i ∈ range (S.sup z + 1), (S.filter (fun v => z v = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_coe.mpr
        (mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_coe.mp hv)))))
    rw [div_eq_one_iff_eq hc.ne']
    exact_mod_cast hcard.symm
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hzero

lemma geqd_eq {N : ℕ} (z : Fin N → ℕ) : geqd z = emp univ z := by
  funext i; simp [geqd, emp]

lemma leqd_eq (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : leqd M G N z w = emp (nbrW M G N w) z := by
  funext i; simp [leqd, emp]

lemma geqd_inX {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℕ) : InX (geqd z) := by
  rw [geqd_eq]
  exact emp_inX _ ⟨⟨0, by omega⟩, mem_univ _⟩ z

lemma l1dist_le_two (a b : ℕ → ℝ) (ha : InX a) (hb : InX b) :
    PowerOfDUniversality.Fluid.l1dist a b ≤ 2 := by
  unfold PowerOfDUniversality.Fluid.l1dist
  have hA : ∑' i, ENNReal.ofReal (a i) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg ha.1 ha.2.summable, ha.2.tsum_eq, ENNReal.ofReal_one]
  have hB : ∑' i, ENNReal.ofReal (b i) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hb.1 hb.2.summable, hb.2.tsum_eq, ENNReal.ofReal_one]
  calc ∑' i, ENNReal.ofReal |a i - b i|
      ≤ ∑' i, (ENNReal.ofReal (a i) + ENNReal.ofReal (b i)) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← ENNReal.ofReal_add (ha.1 i) (hb.1 i)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [abs_le]; constructor <;> linarith [ha.1 i, hb.1 i]
    _ = 2 := by rw [ENNReal.tsum_add, hA, hB]; norm_num

/-- Level-aggregated arrival weight of dispatcher `w`: probability that an arrival at `w`
joins a server with queue length `i`. -/
noncomputable def levW {M : ℕ → ℕ} {N : ℕ} (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (w : Fin (M N)) (z : Fin N → ℕ) (i : ℕ) : ℝ :=
  ∑ v ∈ univ.filter (fun v => z v = i), route w z v

/-- Level-aggregated arrival distribution (dispatcher uniform). -/
noncomputable def levA (M : ℕ → ℕ) (N : ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (z : Fin N → ℕ) (i : ℕ) : ℝ :=
  (1 / (M N : ℝ)) * ∑ w : Fin (M N), levW route w z i

lemma levW_piRoute (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (w : Fin (M N))
    (hw : (nbrW M G N w).Nonempty) (z : Fin N → ℕ) (i : ℕ) :
    levW (piRoute M G N p) w z i = p (leqd M G N z w) i := by
  unfold levW piRoute
  set c := ((nbrW M G N w).filter (fun u => z u = i)).card with hc
  have h1 : ∑ v ∈ univ.filter (fun v => z v = i),
      (if v ∈ nbrW M G N w then p (leqd M G N z w) (z v) /
        (((nbrW M G N w).filter (fun u => z u = z v)).card : ℝ) else 0)
      = ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i), p (leqd M G N z w) i / (c : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
    have hset : (univ.filter (fun v => z v = i ∧ v ∈ nbrW M G N w))
        = (nbrW M G N w).filter (fun u => z u = i) := by
      ext v; simp [and_comm]
    rw [hset]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.mem_filter] at hv
    rw [hv.2]
  rw [h1, Finset.sum_const, nsmul_eq_mul, ← hc]
  by_cases h0 : c = 0
  · have hL : leqd M G N z w i = 0 := by
      simp [leqd, ← hc, h0]
    have hX : InX (leqd M G N z w) := by rw [leqd_eq]; exact emp_inX _ hw z
    rw [(hp _ hX).2.2 i hL, h0]; simp
  · have : (c : ℝ) ≠ 0 := by exact_mod_cast h0
    field_simp

/-- Drift error of the policy routing on `G_N` against the mean-field routing `p(x(z))`:
at most `K (ε M + 2 B^ε_N(z)) / M`. -/
theorem lev_err (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 1 ≤ N)
    (hM : 0 < M N) (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (K : ℝ) (hK : 0 ≤ K)
    (hLip : IsLipschitzPolicyWith p K) (hnbr : ∀ w, (nbrW M G N w).Nonempty)
    (ε : ℝ) (z : Fin N → ℕ) :
    PowerOfDUniversality.Fluid.l1dist (levA M N (piRoute M G N p) z) (p (geqd z)) ≤
      ENNReal.ofReal (K / (M N : ℝ)) *
        ((M N : ℝ≥0∞) * ENNReal.ofReal ε + 2 * (badCount M G N ε z : ℝ≥0∞)) := by
  have hMr : (0 : ℝ) < M N := by exact_mod_cast hM
  have hgX := geqd_inX hN z
  have hLX : ∀ w, InX (leqd M G N z w) := fun w => by rw [leqd_eq]; exact emp_inX _ (hnbr w) z
  have hpt : ∀ i, levA M N (piRoute M G N p) z i - p (geqd z) i
      = (1 / (M N : ℝ)) * ∑ w : Fin (M N), (p (leqd M G N z w) i - p (geqd z) i) := by
    intro i
    unfold levA
    simp only [levW_piRoute M G N p hp _ (hnbr _), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hstep : PowerOfDUniversality.Fluid.l1dist (levA M N (piRoute M G N p) z) (p (geqd z))
      ≤ ENNReal.ofReal (1 / (M N : ℝ)) * ∑ w : Fin (M N),
          PowerOfDUniversality.Fluid.l1dist (p (leqd M G N z w)) (p (geqd z)) := by
    unfold PowerOfDUniversality.Fluid.l1dist
    calc ∑' i, ENNReal.ofReal |levA M N (piRoute M G N p) z i - p (geqd z) i|
        ≤ ∑' i, ∑ w : Fin (M N),
            ENNReal.ofReal (1 / (M N : ℝ)) * ENNReal.ofReal |p (leqd M G N z w) i - p (geqd z) i| := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [hpt i, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (M N : ℝ))]
          calc ENNReal.ofReal (1 / (M N : ℝ) * |∑ w : Fin (M N), (p (leqd M G N z w) i - p (geqd z) i)|)
              ≤ ENNReal.ofReal (1 / (M N : ℝ) * ∑ w : Fin (M N), |p (leqd M G N z w) i - p (geqd z) i|) :=
                ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
                  (by positivity))
            _ = _ := by
                rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun w _ => by positivity)]
                refine Finset.sum_congr rfl fun w _ => ?_
                rw [ENNReal.ofReal_mul (by positivity)]
      _ = _ := by
          first
            | rw [tsum_sum (fun _ _ => ENNReal.summable)]
            | rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [ENNReal.tsum_mul_left]
  have hw : ∀ w, PowerOfDUniversality.Fluid.l1dist (p (leqd M G N z w)) (p (geqd z)) ≤
      ENNReal.ofReal K * (if ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w) then 2 else ENNReal.ofReal ε) := by
    intro w
    refine (hLip _ _ (hLX w) hgX).trans ?_
    gcongr
    split_ifs with h
    · rw [PowerOfDUniversality.Fluid.l1dist] at *
      have := l1dist_le_two _ _ (hLX w) hgX
      exact this
    · push Not at h
      have hsym : PowerOfDUniversality.Fluid.l1dist (leqd M G N z w) (geqd z) =
          PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w) := by
        unfold PowerOfDUniversality.Fluid.l1dist
        congr 1; funext i; rw [abs_sub_comm]
      rw [hsym]; exact h.le
  have hsumw : ∑ w : Fin (M N), (if ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w) then (2 : ℝ≥0∞)
          else ENNReal.ofReal ε) ≤
      (M N : ℝ≥0∞) * ENNReal.ofReal ε + 2 * (badCount M G N ε z : ℝ≥0∞) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hb : ((univ.filter (fun w : Fin (M N) => ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w))).card : ℝ≥0∞)
        = (badCount M G N ε z : ℝ≥0∞) := rfl
    have hg : ((univ.filter (fun w : Fin (M N) => ¬ ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w))).card : ℝ≥0∞)
        ≤ (M N : ℝ≥0∞) := by
      have := Finset.card_filter_le (univ : Finset (Fin (M N))) (fun w : Fin (M N) => ¬ ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w))
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    rw [hb, add_comm, mul_comm (badCount M G N ε z : ℝ≥0∞)]
    gcongr
  calc _ ≤ _ := hstep
    _ ≤ ENNReal.ofReal (1 / (M N : ℝ)) * ∑ w : Fin (M N), ENNReal.ofReal K * (if ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w) then 2 else ENNReal.ofReal ε) := by
        gcongr with w _; exact hw w
    _ ≤ _ := by
        rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [show 1 / (M N : ℝ) * K = K / (M N : ℝ) by ring]
        gcongr

end SC66L

namespace SC66L

open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

lemma nbr_ne (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (N : ℕ) (hN : 1 ≤ N) (w : Fin (M N)) :
    (nbrW M G N w).Nonempty := by
  have hc := hconn N hN
  obtain ⟨p⟩ := hc.preconnected (Sum.inr w) (Sum.inl (⟨0, by omega⟩ : Fin N))
  rcases p with _ | ⟨h, _⟩
  rw [compatGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨_, h | h⟩ := h
  · obtain ⟨v, w', h1, _⟩ := h
    cases h1
  · obtain ⟨v, w', rfl, h2, h3⟩ := h
    cases h2
    exact ⟨v, by simp [nbrW, h3]⟩

lemma piRoute_rule (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hnbr : ∀ w, (nbrW M G N w).Nonempty) :
    IsRoutingRule M G N (piRoute M G N p) := by
  refine ⟨fun w z v => ?_, fun w z v hv => by simp [piRoute, hv], fun w z => ?_⟩
  · have hX : InX (leqd M G N z w) := by rw [leqd_eq]; exact emp_inX _ (hnbr w) z
    unfold piRoute; split_ifs
    · exact div_nonneg ((hp _ hX).1 _) (by positivity)
    · exact le_rfl
  · have hX : InX (leqd M G N z w) := by rw [leqd_eq]; exact emp_inX _ (hnbr w) z
    set B := (univ : Finset (Fin N)).sup z + 1
    have hfib : ∑ v, piRoute M G N p w z v = ∑ i ∈ range B, levW (piRoute M G N p) w z i := by
      unfold levW
      rw [Finset.sum_fiberwise_of_maps_to (g := z) (t := range B)]
      intro v _; exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (mem_univ v)))
    rw [hfib]
    simp only [levW_piRoute M G N p hp w (hnbr w)]
    have hz : ∀ i ∉ range B, p (leqd M G N z w) i = 0 := by
      intro i hi
      simp only [mem_range, not_lt] at hi
      refine (hp _ hX).2.2 i ?_
      have : (nbrW M G N w).filter (fun v => z v = i) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v _ hvi
        have := Finset.le_sup (f := z) (mem_univ v)
        omega
      simp [leqd, this]
    have := (hp _ hX).2.1
    rw [← (hasSum_sum_of_ne_finset_zero hz).unique this]

/-- NEW CHILD (perturbed Kurtz LLN): the LB process with ANY routing law whose level-aggregated
arrival law stays within `η` of `p(x(z))` on `[0,T]` w.h.p. follows the (4.2) trajectory. -/
def PLLNStmt : Prop :=
  ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (M : ℕ → ℕ), (∀ N, 0 < M N) →
  ∀ (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ),
  (∀ N, 1 ≤ N → (∀ w z v, 0 ≤ route N w z v) ∧ ∀ w z, ∑ v, route N w z v = 1) →
  ∀ (p : (ℕ → ℝ) → ℕ → ℝ), IsAssignmentFn p → IsLipschitzPolicy p →
  ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
  Tendsto (fun N => l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
  ∀ (s : ℝ → ℕ → ℝ), IsPiTrajectory lam p s → (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
    (∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N)) →
    ∀ T : ℝ, 0 ≤ T →
    (∀ η : ℝ, 0 < η → Tendsto (fun N => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal η ≤
        l1dist (levA M N (route N) (statePath (Y N) (τ N) ω t))
          (p (geqd (statePath (Y N) (τ N) ω t)))}) atTop (𝓝 0)) →
    ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
        supDistL1 (occPath (Y N) (τ N) ω) s T}) atTop (𝓝 0)

/-- Proposition 4.5 (Proved on the platform, f2badd14) as a Prop. -/
def P45Stmt : Prop :=
  ∀ (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → IsRoutingRule M G N (route N))
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N)),
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ T : ℝ, 0 ≤ T →
      Tendsto (fun N => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          δ * (M N : ℝ) ≤ (badCount M G N ε (statePath (Y N) (τ N) ω t) : ℝ)})
        atTop (𝓝 0)

lemma err_small (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 1 ≤ N)
    (hM : 0 < M N) (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (K : ℝ) (hK : 0 ≤ K)
    (hLip : IsLipschitzPolicyWith p K) (hnbr : ∀ w, (nbrW M G N w).Nonempty)
    (ε δ η : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hη : K * (ε + 2 * δ) < η) (z : Fin N → ℕ)
    (hbad : (badCount M G N ε z : ℝ) < δ * (M N : ℝ)) :
    l1dist (levA M N (piRoute M G N p) z) (p (geqd z)) < ENNReal.ofReal η := by
  have hMr : (0 : ℝ) < M N := by exact_mod_cast hM
  refine (lev_err M G N hN hM p hp K hK hLip hnbr ε z).trans_lt ?_
  have h1 : ((M N : ℝ≥0∞) * ENNReal.ofReal ε + 2 * (badCount M G N ε z : ℝ≥0∞)) =
      ENNReal.ofReal ((M N : ℝ) * ε + 2 * (badCount M G N ε z : ℝ)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    norm_num
  rw [h1, ← ENNReal.ofReal_mul (by positivity)]
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) hη
  rw [ENNReal.ofReal_lt_ofReal_iff hη0]
  calc K / (M N : ℝ) * ((M N : ℝ) * ε + 2 * (badCount M G N ε z : ℝ))
      ≤ K / (M N : ℝ) * ((M N : ℝ) * ε + 2 * (δ * (M N : ℝ))) := by gcongr
    _ = K * (ε + 2 * δ) := by field_simp
    _ < η := hη

end SC66L

namespace SC66L

open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

/-- Assembly: theorem_4_3 from the perturbed LLN child and Proposition 4.5. -/
theorem assemble2 (h : PLLNStmt) (h45 : P45Stmt) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hLip : IsLipschitzPolicy p)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (hs0 : s 0 = q₀)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (piRoute M G N p) (z₀ N) (Y N) (τ N)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤ supDistL1 (occPath (Y N) (τ N) ω) s T})
        atTop (𝓝 0) := by
  intro T hT ε hε
  obtain ⟨K, hK0, hKL⟩ := hLip
  have hnbr : ∀ N, 1 ≤ N → ∀ w, (nbrW M G N w).Nonempty := fun N hN w => nbr_ne M G hconn N hN w
  have hrule : ∀ N, 1 ≤ N → IsRoutingRule M G N (piRoute M G N p) :=
    fun N hN => piRoute_rule M G N p hp (hnbr N hN)
  refine h lam hlam0 hlam1 M hM (fun N => piRoute M G N p)
    (fun N hN => ⟨(hrule N hN).1, (hrule N hN).2.2⟩) p hp ⟨K, hK0, hKL⟩ z₀ q₀ hq₀ hinit s hs hsY hs0
    Ω P Y τ hproc T hT ?_ ε hε
  intro η hη
  set c := η / (4 * (K + 1)) with hcdef
  have hc : 0 < c := by positivity
  have key : K * (c + 2 * c) < η := by
    have h1 : K * (c + 2 * c) = (3 * K / (4 * (K + 1))) * η := by
      rw [hcdef]; field_simp; ring
    have h2 : 3 * K / (4 * (K + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    rw [h1]; exact mul_lt_of_lt_one_left hη h2
  have h45' := h45 lam hlam0 hlam1 M hM G hconn hsparse (fun N => piRoute M G N p) hrule
    z₀ q₀ hq₀ hinit Ω P Y τ hproc c hc c hc T hT
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h45'
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  refine measure_mono ?_
  intro ω hω
  obtain ⟨t, ht, hle⟩ := hω
  refine ⟨t, ht, ?_⟩
  by_contra hlt
  push Not at hlt
  exact absurd hle (not_le.mpr (err_small M G N hN (hM N) p hp K hK0.le hKL (hnbr N hN)
    c c η hc.le hc.le key _ hlt))

end SC66L

open StrictCompatLB.MeanField in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hLip : IsLipschitzPolicy p)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (hs0 : s 0 = q₀)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (piRoute M G N p) (z₀ N) (Y N) (τ N)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
        atTop (𝓝 0) := by
  exact SC66L.assemble2 (fun lam hlam0 hlam1 M hM route hroute p hp hLip z₀ q₀ hq₀ hinit s hs hsY hs0
      Ω _ P Y τ hproc T hT hlev ε hε =>
      perturbed_meanfield_lln lam hlam0 hlam1 M hM route hroute p hp hLip z₀ q₀ hq₀ hinit s hs hsY hs0
        Ω P Y τ hproc T hT hlev ε hε)
    (fun lam hlam0 hlam1 M hM G hconn hsparse route hroute z₀ q₀ hq₀ hinit Ω _ P Y τ hproc =>
      proposition_4_5 lam hlam0 hlam1 M hM G hconn hsparse route hroute z₀ q₀ hq₀ hinit Ω P Y τ hproc)
    lam hlam0 hlam1 M hM G hconn hsparse p hp hLip z₀ q₀ hq₀ hinit s hs hsY hs0 Ω P Y τ hproc
