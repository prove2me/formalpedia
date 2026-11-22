-- Prove2me | solution 1 for RoundedPotentials.Main.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T20:10:15.505271+00:00
-- url     : https://prove2.me/submissions/967774c1-ff49-4b81-a3dc-1150714cc17d

import Definitions.Def_RoundedPotentials_Main_Verifier
import Theorems.Thm_FlowsNetworks_MaxFlow_max_flow_min_cut

/-! ===== RP_Bridge ===== -/

/-! # Piece D — bridge between `RoundedPotentials.Main` and `FlowsNetworks.MaxFlow`

Statements are FIXED (other files depend on them). Fill in the proofs only. -/

namespace RPBridge
open RoundedPotentials.Main FlowsNetworks.MaxFlow
open scoped BigOperators

variable {n W : ℕ}

theorem sum_filter_fst_eq (G : Network (Fin n)) {f : Assignment n}
    (hf : SupportedOnArcs G f) (x : Fin n) :
    (∑ p ∈ G.arcs.filter (fun p => p.1 = x), f p.1 p.2) = ∑ u, f x u := by
  rw [Finset.sum_subset (Finset.filter_subset_filter _ (Finset.subset_univ G.arcs))]
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp
  · intro p hp1 hp
    apply hf
    intro hmem
    apply hp
    simp only [Finset.mem_filter] at *
    exact ⟨hmem, hp1.2⟩

theorem sum_filter_snd_eq (G : Network (Fin n)) {f : Assignment n}
    (hf : SupportedOnArcs G f) (x : Fin n) :
    (∑ p ∈ G.arcs.filter (fun p => p.2 = x), f p.1 p.2) = ∑ u, f u x := by
  rw [Finset.sum_subset (Finset.filter_subset_filter _ (Finset.subset_univ G.arcs))]
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp
  · intro p hp1 hp
    apply hf
    intro hmem
    apply hp
    simp only [Finset.mem_filter] at *
    exact ⟨hmem, hp1.2⟩

theorem network_cap (I : Instance n W) (u v : Fin n) :
    (network I).cap u v = (capNat I u v : ℝ) := rfl

/-- Off the arc set, the capacity is zero. -/
theorem capNat_eq_zero_of_not_mem (I : Instance n W) {u v : Fin n}
    (h : (u, v) ∉ (network I).arcs) : capNat I u v = 0 := by
  unfold capNat
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  split_ifs with h1
  · exfalso; apply h
    simp only [network, List.mem_toFinset, List.mem_map]
    exact ⟨e, he, Prod.ext h1.1 h1.2⟩
  · rfl

/-- A capacity-feasible assignment is supported on the arcs of `network I`. -/
theorem supportedOnArcs_of_capacityFeasible (I : Instance n W) {f : Assignment n}
    (hf : CapacityFeasible I f) : SupportedOnArcs (network I) f := by
  intro x y h
  obtain ⟨h1, h2⟩ := hf x y
  rw [capNat_eq_zero_of_not_mem I h, Nat.cast_zero] at h2
  linarith

/-- For any network on `Fin n`, net outflow agrees with `excess` for arc-supported functions. -/
theorem netFlowOut_eq_excess (G : Network (Fin n)) {f : Assignment n}
    (hf : SupportedOnArcs G f) (v : Fin n) : netFlowOut G f v = excess f v := by
  unfold netFlowOut excess
  rw [sum_filter_fst_eq G hf, sum_filter_snd_eq G hf]

theorem clip_nonneg (z : ℝ) : 0 ≤ clip z := by
  unfold clip; exact le_min zero_le_one (le_max_left _ _)

theorem clip_le_one (z : ℝ) : clip z ≤ 1 := by
  unfold clip; exact min_le_left _ _

theorem clip_of_one_le {z : ℝ} (hz : 1 ≤ z) : clip z = 1 := by
  unfold clip; rw [max_eq_right (by linarith), min_eq_left hz]

theorem clip_of_nonpos {z : ℝ} (hz : z ≤ 0) : clip z = 0 := by
  unfold clip; rw [max_eq_left hz, min_eq_right zero_le_one]

/-- The induced assignment of any potential is capacity-feasible. -/
theorem capacityFeasible_induced (I : Instance n W) (y : Fin n → ℝ) :
    CapacityFeasible I (induced I y) := by
  intro u v
  unfold induced
  have h0 := clip_nonneg (y u - y v)
  have h1 := clip_le_one (y u - y v)
  have hc : (0 : ℝ) ≤ capNat I u v := Nat.cast_nonneg _
  constructor
  · positivity
  · nlinarith

/-- Cut capacities of `network I` are natural numbers. -/
theorem cutCapacity_natCast (I : Instance n W) (X : Finset (Fin n)) :
    ∃ k : ℕ, cutCapacity (network I) X = (k : ℝ) := by
  refine ⟨∑ p ∈ arcsBetween (network I) X Xᶜ, capNat I p.1 p.2, ?_⟩
  unfold cutCapacity arcSum
  rw [Nat.cast_sum]
  rfl

/-- `IsFlow` on `network I`, restated in the certificate vocabulary. -/
theorem isFlow_iff (I : Instance n W) {s t : Fin n} (hst : s ≠ t) (f : Assignment n) (w : ℝ) :
    IsFlow (network I) s t f w ↔
      SupportedOnArcs (network I) f ∧ CapacityFeasible I f ∧ HasExcess f (target s t w) := by
  have key : ∀ g : Assignment n, SupportedOnArcs (network I) g →
      (Conservation (network I) s t g w ↔ HasExcess g (target s t w)) := by
    intro g hg
    unfold Conservation HasExcess target
    simp only [netFlowOut_eq_excess _ hg]
    constructor
    · rintro ⟨hs, ht, ho⟩ v
      by_cases hvs : v = s
      · subst hvs; simp [hst, hs]
      · by_cases hvt : v = t
        · subst hvt; simp [hvs, ht]
        · simp [hvs, hvt, ho v hvs hvt]
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · simpa [hst] using h s
      · simpa [Ne.symm hst] using h t
      · intro x hxs hxt; simpa [hxs, hxt] using h x
  constructor
  · rintro ⟨hsup, hnn, hcap, hcons⟩
    refine ⟨hsup, ?_, (key f hsup).1 hcons⟩
    intro u v
    by_cases huv : (u, v) ∈ (network I).arcs
    · exact ⟨hnn _ huv, hcap _ huv⟩
    · rw [hsup u v huv, capNat_eq_zero_of_not_mem I huv]; simp
  · rintro ⟨hsup, hcf, hex⟩
    exact ⟨hsup, fun p _ => (hcf p.1 p.2).1, fun p _ => (hcf p.1 p.2).2, (key f hsup).2 hex⟩

end RPBridge

/-! ===== RP_Cut ===== -/

/-! # Piece E — cut cancellation and cut bounds (generic networks)

Statements are FIXED (other files depend on them). Fill in the proofs only. -/

namespace RPCut
open FlowsNetworks.MaxFlow
open scoped BigOperators

variable {N : Type} [Fintype N] [DecidableEq N]

/-- eq. (3), cut cancellation: summing net outflow over `X` cancels arcs inside `X`. -/
theorem sum_netFlowOut (G : Network N) (f : N → N → ℝ) (X : Finset N) :
    ∑ x ∈ X, netFlowOut G f x = arcSum G f X Xᶜ - arcSum G f Xᶜ X := by
  classical
  have key : ∀ (h : N × N → N),
      ∑ x ∈ X, ∑ p ∈ G.arcs.filter (fun p => h p = x), f p.1 p.2 =
        ∑ p ∈ G.arcs, if h p ∈ X then f p.1 p.2 else 0 := by
    intro h
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_ite_eq]
  unfold netFlowOut
  rw [Finset.sum_sub_distrib, key (fun p => p.1), key (fun p => p.2)]
  unfold arcSum arcsBetween
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h1 : p.1 ∈ X <;> by_cases h2 : p.2 ∈ X <;> simp [h1, h2]

/-- For a capacity-feasible arc function, the net outflow of `X` is at most `c(X, X̄)`. -/
theorem sum_netFlowOut_le_cutCapacity (G : Network N) (g : N → N → ℝ)
    (hnn : ∀ p ∈ G.arcs, 0 ≤ g p.1 p.2) (hle : ∀ p ∈ G.arcs, g p.1 p.2 ≤ G.cap p.1 p.2)
    (X : Finset N) :
    ∑ x ∈ X, netFlowOut G g x ≤ cutCapacity G X := by
  rw [sum_netFlowOut]
  unfold cutCapacity
  have h1 : arcSum G g X Xᶜ ≤ arcSum G G.cap X Xᶜ := by
    unfold arcSum
    refine Finset.sum_le_sum (fun p hp => hle p ?_)
    exact (Finset.mem_filter.mp hp).1
  have h2 : 0 ≤ arcSum G g Xᶜ X := by
    unfold arcSum
    refine Finset.sum_nonneg (fun p hp => hnn p ?_)
    exact (Finset.mem_filter.mp hp).1
  linarith

/-- If `g` saturates every arc leaving `X` and vanishes on every arc entering `X`, the net
outflow of `X` equals `c(X, X̄)`. -/
theorem sum_netFlowOut_eq_cutCapacity (G : Network N) (g : N → N → ℝ) (X : Finset N)
    (hsat : ∀ p ∈ arcsBetween G X Xᶜ, g p.1 p.2 = G.cap p.1 p.2)
    (hzero : ∀ p ∈ arcsBetween G Xᶜ X, g p.1 p.2 = 0) :
    ∑ x ∈ X, netFlowOut G g x = cutCapacity G X := by
  rw [sum_netFlowOut]
  unfold cutCapacity
  have h1 : arcSum G g X Xᶜ = arcSum G G.cap X Xᶜ := Finset.sum_congr rfl hsat
  have h2 : arcSum G g Xᶜ X = 0 := Finset.sum_eq_zero hzero
  rw [h1, h2, sub_zero]

/-- A conserving function of value `v` has net outflow `v` across any `s`–`t` cut. -/
theorem sum_netFlowOut_of_conservation (G : Network N) {s t : N} (hst : s ≠ t)
    {f : N → N → ℝ} {v : ℝ} (hc : Conservation G s t f v) {X : Finset N}
    (hs : s ∈ X) (ht : t ∉ X) :
    ∑ x ∈ X, netFlowOut G f x = v := by
  obtain ⟨h1, -, h3⟩ := hc
  rw [← Finset.add_sum_erase X _ hs, h1, Finset.sum_eq_zero, add_zero]
  intro x hx
  have hxs : x ≠ s := Finset.ne_of_mem_erase hx
  have hxt : x ≠ t := fun h => ht (h ▸ Finset.mem_of_mem_erase hx)
  exact h3 x hxs hxt

/-- Weak duality: every flow value is at most every cut capacity. -/
theorem flow_le_cutCapacity (G : Network N) {s t : N} (hst : s ≠ t)
    {f : N → N → ℝ} {v : ℝ} (hf : IsFlow G s t f v) {X : Finset N}
    (hs : s ∈ X) (ht : t ∉ X) :
    v ≤ cutCapacity G X := by
  obtain ⟨-, hnn, hle, hc⟩ := hf
  rw [← sum_netFlowOut_of_conservation G hst hc hs ht]
  exact sum_netFlowOut_le_cutCapacity G f hnn hle X

end RPCut

/-! ===== RP_Sound ===== -/

/-! # Piece F — soundness (Lemma 3.1 and Lemma 3.2)

Statements are FIXED. Fill in the proofs only. While D/E are in progress this file imports
frozen `_Stub` copies of `RP_Bridge` / `RP_Cut`; the imports get switched at integration. -/

namespace RPSound
open RoundedPotentials.Main FlowsNetworks.MaxFlow
open scoped BigOperators

variable {n W : ℕ}

/-- Σ over an `s`–`t` cut of the target vector is `p`. -/
theorem sum_target {s t : Fin n} (hst : s ≠ t) (p : ℝ) {X : Finset (Fin n)}
    (hs : s ∈ X) (ht : t ∉ X) :
    ∑ v ∈ X, target s t p v = p := by
  rw [Finset.sum_eq_single s]
  · simp [target, hst]
  · intro v hv hvs
    have hvt : v ≠ t := fun h => ht (h ▸ hv)
    simp [target, hvs, hvt]
  · intro h; exact absurd hs h

/-- Helper: the excess sum over a cut is within `1/8` of `p`. -/
theorem sum_excess_bounds {s t : Fin n} (hst : s ≠ t) {N : ℕ} (hN : n ≤ N)
    (p : ℝ) (g : Assignment n)
    (hex : ∀ v, |excess g v - target s t p v| ≤ epsilon N)
    {X : Finset (Fin n)} (hs : s ∈ X) (ht : t ∉ X) :
    p - 1/8 ≤ ∑ v ∈ X, excess g v ∧ ∑ v ∈ X, excess g v ≤ p + 1/8 := by
  have hNpos : (0 : ℝ) < N := by
    have := Fin.pos s
    exact_mod_cast lt_of_lt_of_le this hN
  have hcard : (X.card : ℝ) ≤ N := by
    have h1 : X.card ≤ n := by
      simpa using Finset.card_le_univ X
    exact_mod_cast h1.trans hN
  have hce : (X.card : ℝ) * epsilon N ≤ 1/8 := by
    unfold epsilon
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hT := sum_target hst p hs ht
  constructor
  · have : ∑ v ∈ X, (target s t p v - epsilon N) ≤ ∑ v ∈ X, excess g v :=
      Finset.sum_le_sum fun v _ => by linarith [(abs_le.mp (hex v)).1]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hT] at this
    linarith
  · have : ∑ v ∈ X, excess g v ≤ ∑ v ∈ X, (target s t p v + epsilon N) :=
      Finset.sum_le_sum fun v _ => by linarith [(abs_le.mp (hex v)).2]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hT] at this
    linarith

/-- Lemma 3.1, cut form: a capacity-feasible assignment that is within `1/(8N)` of conserving
`p` (with `n ≤ N`) forces every `s`–`t` cut to have capacity at least `p`. -/
theorem lemma_3_1_cut (I : Instance n W) {s t : Fin n} (hst : s ≠ t) {N : ℕ} (hN : n ≤ N)
    (p : ℤ) (g : Assignment n) (hg : CapacityFeasible I g)
    (hex : ∀ v, |excess g v - target s t (p : ℝ) v| ≤ epsilon N)
    (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X) :
    (p : ℝ) ≤ cutCapacity (network I) X := by
  have hsup := RPBridge.supportedOnArcs_of_capacityFeasible I hg
  have hle := RPCut.sum_netFlowOut_le_cutCapacity (network I) g
    (fun q _ => (hg q.1 q.2).1)
    (fun q _ => by rw [RPBridge.network_cap]; exact (hg q.1 q.2).2) X
  rw [Finset.sum_congr rfl (fun v _ => RPBridge.netFlowOut_eq_excess _ hsup v)] at hle
  have hb := (sum_excess_bounds hst hN (p : ℝ) g hex hs ht).1
  obtain ⟨k, hk⟩ := RPBridge.cutCapacity_natCast I X
  rw [hk] at hle ⊢
  have h1 : ((p : ℤ) : ℝ) < ((k : ℤ) + 1 : ℤ) := by push_cast; linarith
  have h2 : p ≤ (k : ℤ) := Int.lt_add_one_iff.mp (Int.cast_lt.mp h1)
  exact_mod_cast h2

/-- Lemma 3.1: under the same hypotheses some flow has value at least `p`. -/
theorem lemma_3_1 (I : Instance n W) {s t : Fin n} (hst : s ≠ t) {N : ℕ} (hN : n ≤ N)
    (p : ℤ) (g : Assignment n) (hg : CapacityFeasible I g)
    (hex : ∀ v, |excess g v - target s t (p : ℝ) v| ≤ epsilon N) :
    ∃ (f : Assignment n) (w : ℝ), IsFlow (network I) s t f w ∧ (p : ℝ) ≤ w := by
  obtain ⟨v, ⟨⟨f, hf⟩, _⟩, ⟨⟨X, hs, ht, hv⟩, _⟩⟩ := max_flow_min_cut (network I) s t hst
  refine ⟨f, v, hf, ?_⟩
  rw [hv]
  exact lemma_3_1_cut I hst hN p g hg hex X hs ht

/-- Lemma 3.2 (single-pair correctness / soundness): if the interval conditions and excess
checks pass for potentials `y`, the maximum flow value is exactly `p`. -/
theorem lemma_3_2 (I : Instance n W) {s t : Fin n} (hst : s ≠ t) {N : ℕ} (hN : n ≤ N)
    (p : ℤ) (y : Fin n → ℝ) (h : CertificateChecks I N s t p y) :
    MaxValue I s t (p : ℝ) := by
  obtain ⟨⟨hint, hys, hyt⟩, hex⟩ := h
  have hg := RPBridge.capacityFeasible_induced I y
  set X : Finset (Fin n) := Finset.univ.filter (fun v => (N : ℝ) ≤ y v) with hX
  have hs : s ∈ X := by simp [hX, hys]
  have ht : t ∉ X := by simp [hX]; linarith
  have hsat : ∀ q ∈ arcsBetween (network I) X Xᶜ,
      induced I y q.1 q.2 = (network I).cap q.1 q.2 := by
    intro q hq
    simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl, hX, Finset.mem_univ,
      true_and] at hq
    obtain ⟨_, h1, h2⟩ := hq
    have h3 : y q.2 ≤ (N : ℝ) - 1 := by
      rcases hint q.2 with h | h
      · exact h.2
      · exact absurd h.1 h2
    rw [RPBridge.network_cap, induced, RPBridge.clip_of_one_le (by linarith), mul_one]
  have hzero : ∀ q ∈ arcsBetween (network I) Xᶜ X, induced I y q.1 q.2 = 0 := by
    intro q hq
    simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl, hX, Finset.mem_univ,
      true_and] at hq
    obtain ⟨_, h1, h2⟩ := hq
    rw [induced, RPBridge.clip_of_nonpos (by linarith [not_le.mp h1]), mul_zero]
  have heq := RPCut.sum_netFlowOut_eq_cutCapacity (network I) (induced I y) X hsat hzero
  have hsup := RPBridge.supportedOnArcs_of_capacityFeasible I hg
  rw [Finset.sum_congr rfl (fun v _ => RPBridge.netFlowOut_eq_excess _ hsup v)] at heq
  obtain ⟨hlo, hhi⟩ := sum_excess_bounds hst hN (p : ℝ) _ hex hs ht
  obtain ⟨k, hk⟩ := RPBridge.cutCapacity_natCast I X
  have hcut : cutCapacity (network I) X = (p : ℝ) := by
    rw [hk] at heq ⊢
    have h1 : ((p : ℤ) : ℝ) < ((k : ℤ) + 1 : ℤ) := by push_cast; linarith
    have h2 : ((k : ℤ) : ℝ) < ((p + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h1' : p ≤ (k : ℤ) := Int.lt_add_one_iff.mp (Int.cast_lt.mp h1)
    have h2' : (k : ℤ) ≤ p := Int.lt_add_one_iff.mp (Int.cast_lt.mp h2)
    have : (k : ℤ) = p := le_antisymm h2' h1'
    rw [← this]; push_cast; rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨f, w, hf, hpw⟩ := lemma_3_1 I hst hN p _ hg hex
    have hw : w ≤ (p : ℝ) := hcut ▸ RPCut.flow_le_cutCapacity (network I) hst hf hs ht
    have : w = (p : ℝ) := le_antisymm hw hpw
    exact ⟨f, this ▸ hf⟩
  · rintro w ⟨f, hf⟩
    exact hcut ▸ RPCut.flow_le_cutCapacity (network I) hst hf hs ht

end RPSound

/-! ===== RP_CompDefs ===== -/

/-! # Shared definitions for the completeness half (G1–G4). FIXED — do not edit. -/

namespace RPComp
open RoundedPotentials.Main FlowsNetworks.MaxFlow
open scoped BigOperators

variable {n W : ℕ}

/-- eq. (8): energy `Φ(f) = Σ_{c_uv > 0} f_uv² / (2 c_uv)`. -/
noncomputable def energy (I : Instance n W) (f : Assignment n) : ℝ :=
  ∑ u, ∑ v, if capNat I u v = 0 then 0 else f u v ^ 2 / (2 * (capNat I u v : ℝ))

/-- Residual move `u → v`: either increase `f u v` (room left) or decrease `f v u` (positive). -/
def ResArc (I : Instance n W) (f : Assignment n) (u v : Fin n) : Prop :=
  f u v < (capNat I u v : ℝ) ∨ 0 < f v u

/-- Length of the residual move `u → v`: the smaller of the available move lengths,
forward `f u v / c u v` and backward `-(f v u / c v u)`; an unavailable move counts as `1`
(never smaller than an available one for a capacity-feasible `f`). -/
noncomputable def resLen (I : Instance n W) (f : Assignment n) (u v : Fin n) : ℝ :=
  min (if f u v < (capNat I u v : ℝ) then f u v / (capNat I u v : ℝ) else 1)
      (if 0 < f v u then -(f v u / (capNat I v u : ℝ)) else 1)

/-- Consecutive pairs of a cyclic vertex list, closing up last → first. -/
def cycPairs (l : List (Fin n)) : List (Fin n × Fin n) := l.zip (l.rotate 1)

/-- A simple directed cycle in the relation `R`. -/
def IsSimpleCycle (R : Fin n → Fin n → Prop) (l : List (Fin n)) : Prop :=
  l ≠ [] ∧ l.Nodup ∧ ∀ e ∈ cycPairs l, R e.1 e.2

/-- Total length of a cyclic vertex list. -/
noncomputable def cycLen (ℓ : Fin n → Fin n → ℝ) (l : List (Fin n)) : ℝ :=
  ((cycPairs l).map fun e => ℓ e.1 e.2).sum

def NoNegCycle (R : Fin n → Fin n → Prop) (ℓ : Fin n → Fin n → ℝ) : Prop :=
  ∀ l, IsSimpleCycle R l → 0 ≤ cycLen ℓ l

end RPComp

/-! ===== RP_MinEnergy ===== -/

/-! # G1 — existence of a minimum-energy flow (§3.2, eq. (8)). Statement FIXED. -/

namespace RPComp
open RoundedPotentials.Main FlowsNetworks.MaxFlow
open scoped BigOperators

variable {n W : ℕ}

theorem continuous_energy (I : Instance n W) : Continuous (energy I) := by
  unfold energy
  refine continuous_finsetSum _ fun u _ => continuous_finsetSum _ fun v _ => ?_
  split_ifs
  · exact continuous_const
  · exact ((continuous_apply_apply u v).pow 2).div_const _

theorem continuous_netFlowOut (I : Instance n W) (x : Fin n) :
    Continuous fun f : Assignment n => netFlowOut (network I) f x := by
  unfold netFlowOut
  refine Continuous.sub (continuous_finsetSum _ fun p _ => ?_)
    (continuous_finsetSum _ fun p _ => ?_) <;> exact continuous_apply_apply _ _

theorem isClosed_flows (I : Instance n W) (s t : Fin n) (p : ℝ) :
    IsClosed {f : Assignment n | IsFlow (network I) s t f p} := by
  simp only [IsFlow, SupportedOnArcs, Conservation, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply_apply x y) continuous_const).inter
    ((isClosed_biInter fun q _ =>
      isClosed_le continuous_const (continuous_apply_apply q.1 q.2)).inter
    ((isClosed_biInter fun q _ =>
      isClosed_le (continuous_apply_apply q.1 q.2) continuous_const).inter
    ((isClosed_eq (continuous_netFlowOut I s) continuous_const).inter
    ((isClosed_eq (continuous_netFlowOut I t) continuous_const).inter
      (isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_eq (continuous_netFlowOut I x) continuous_const)))))

theorem flows_subset_box (I : Instance n W) (s t : Fin n) (p : ℝ) :
    {f : Assignment n | IsFlow (network I) s t f p} ⊆
      Set.pi Set.univ fun u => Set.pi Set.univ fun v => Set.Icc (0 : ℝ) (capNat I u v) := by
  intro f hf u _ v _
  obtain ⟨hsup, hnn, hcap, -⟩ := hf
  by_cases h : (u, v) ∈ (network I).arcs
  · exact ⟨hnn _ h, hcap _ h⟩
  · rw [hsup u v h]; exact ⟨le_rfl, Nat.cast_nonneg _⟩

theorem isCompact_flows (I : Instance n W) (s t : Fin n) (p : ℝ) :
    IsCompact {f : Assignment n | IsFlow (network I) s t f p} :=
  (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
    (isClosed_flows I s t p) (flows_subset_box I s t p)


theorem exists_min_energy (I : Instance n W) {s t : Fin n} (hst : s ≠ t) {p : ℝ}
    (hex : ∃ f, IsFlow (network I) s t f p) :
    ∃ f, IsFlow (network I) s t f p ∧
      ∀ g, IsFlow (network I) s t g p → energy I f ≤ energy I g := by
  obtain ⟨f, hf, hmin⟩ := (isCompact_flows I s t p).exists_isMinOn hex
    (continuous_energy I).continuousOn
  exact ⟨f, hf, fun g hg => hmin hg⟩

end RPComp

/-! ===== RP_NoNegCycle ===== -/

/-! # G2 — Lemma 3.3: no negative residual cycle at a minimum-energy flow. Statements FIXED. -/

namespace RPComp
open RoundedPotentials.Main FlowsNetworks.MaxFlow
open scoped BigOperators
open Filter Topology

variable {n W : ℕ}

/-- Directional derivative of the energy. -/
noncomputable def dEnergy (I : Instance n W) (f D : Assignment n) : ℝ :=
  ∑ u, ∑ v, if capNat I u v = 0 then 0 else f u v / (capNat I u v : ℝ) * D u v

noncomputable def quadE (I : Instance n W) (D : Assignment n) : ℝ :=
  ∑ u, ∑ v, if capNat I u v = 0 then 0 else D u v ^ 2 / (2 * (capNat I u v : ℝ))

theorem quadE_nonneg (I : Instance n W) (D : Assignment n) : 0 ≤ quadE I D := by
  unfold quadE
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => ?_
  split_ifs
  · exact le_rfl
  · positivity

theorem energy_add (I : Instance n W) (f D : Assignment n) (δ : ℝ) :
    energy I (fun u v => f u v + δ * D u v) = energy I f + δ * dEnergy I f D + δ ^ 2 * quadE I D := by
  unfold energy dEnergy quadE
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs with h
  · ring
  · have : (capNat I u v : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp
    ring

theorem excess_add_smul (f D : Assignment n) (δ : ℝ) (x : Fin n) :
    excess (fun u v => f u v + δ * D u v) x = excess f x + δ * excess D x := by
  unfold excess
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem tendsto_line (a b : ℝ) :
    Tendsto (fun δ : ℝ => a + δ * b) (𝓝[>] 0) (𝓝 a) := by
  have : Continuous (fun δ : ℝ => a + δ * b) := by fun_prop
  have h := this.tendsto 0
  simp only [zero_mul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem descent (I : Instance n W) {f : Assignment n} (hf : CapacityFeasible I f)
    (D : Assignment n) (hex : ∀ x, excess D x = 0)
    (hpos : ∀ u v, 0 < D u v → f u v < (capNat I u v : ℝ))
    (hneg : ∀ u v, D u v < 0 → 0 < f u v) (hL : dEnergy I f D < 0) :
    ∃ g, CapacityFeasible I g ∧ (∀ x, excess g x = excess f x) ∧ energy I g < energy I f := by
  have hδpos : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  have hcoord : ∀ u v, ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 ≤ f u v + δ * D u v ∧ f u v + δ * D u v ≤ (capNat I u v : ℝ) := by
    intro u v
    obtain ⟨h0, h1⟩ := hf u v
    refine Eventually.and ?_ ?_
    · rcases le_or_gt 0 (D u v) with hD | hD
      · filter_upwards [hδpos] with δ hδ
        have := mul_nonneg hδ.le hD
        linarith
      · exact ((tendsto_line _ _).eventually_const_lt (hneg u v hD)).mono fun _ h => h.le
    · rcases le_or_gt (D u v) 0 with hD | hD
      · filter_upwards [hδpos] with δ hδ
        have := mul_nonpos_of_nonneg_of_nonpos hδ.le hD
        linarith
      · exact ((tendsto_line _ _).eventually_lt_const (hpos u v hD)).mono fun _ h => h.le
  have hall : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ u v,
      0 ≤ f u v + δ * D u v ∧ f u v + δ * D u v ≤ (capNat I u v : ℝ) := by
    rw [eventually_all]; intro u; rw [eventually_all]; exact hcoord u
  have hE : ∀ᶠ δ in 𝓝[>] (0:ℝ), dEnergy I f D + δ * quadE I D < 0 :=
    (tendsto_line _ _).eventually_lt_const hL
  obtain ⟨δ, hδ, hc, he⟩ := (hδpos.and (hall.and hE)).exists
  refine ⟨fun u v => f u v + δ * D u v, hc, fun x => by rw [excess_add_smul, hex]; ring, ?_⟩
  rw [energy_add]
  have : δ * (dEnergy I f D + δ * quadE I D) < 0 := mul_neg_of_pos_of_neg hδ he
  nlinarith


/-- Whether the forward move realises `resLen` on the pair `u → v`. -/
def FwdP (I : Instance n W) (f : Assignment n) (u v : Fin n) : Prop :=
  f u v < (capNat I u v : ℝ) ∧ (0 < f v u → f u v / (capNat I u v : ℝ) ≤ -(f v u / (capNat I v u : ℝ)))

open Classical in
/-- The unit move chosen on the pair `e`. -/
noncomputable def move (I : Instance n W) (f : Assignment n) (e : Fin n × Fin n) : Assignment n :=
  if FwdP I f e.1 e.2 then fun x y => if x = e.1 then (if y = e.2 then 1 else 0) else 0
  else fun x y => if x = e.2 then (if y = e.1 then -1 else 0) else 0

theorem excess_move (I : Instance n W) (f : Assignment n) (e : Fin n × Fin n) (x : Fin n) :
    excess (move I f e) x = (if x = e.1 then 1 else 0) - (if x = e.2 then 1 else 0) := by
  unfold move excess
  split_ifs <;> simp_all


theorem excess_listSum {α : Type*} (L : List α) (g : α → Assignment n) (x : Fin n) :
    excess (fun a b => (L.map fun e => g e a b).sum) x = (L.map fun e => excess (g e) x).sum := by
  induction L with
  | nil => simp [excess]
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    unfold excess
    simp only [Finset.sum_add_distrib]
    ring

theorem dEnergy_listSum {α : Type*} (I : Instance n W) (f : Assignment n) (L : List α)
    (g : α → Assignment n) :
    dEnergy I f (fun a b => (L.map fun e => g e a b).sum) = (L.map fun e => dEnergy I f (g e)).sum := by
  induction L with
  | nil => simp [dEnergy]
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    unfold dEnergy
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring

theorem list_sum_map_sub {α : Type*} (L : List α) (a b : α → ℝ) :
    (L.map fun e => a e - b e).sum = (L.map a).sum - (L.map b).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem cyc_telescope (l : List (Fin n)) (x : Fin n) :
    ((cycPairs l).map fun e => (if x = e.1 then (1:ℝ) else 0) - (if x = e.2 then 1 else 0)).sum = 0 := by
  unfold cycPairs
  rw [list_sum_map_sub]
  have h1 : (l.zip (l.rotate 1)).map (fun e => if x = e.1 then (1:ℝ) else 0)
      = l.map (fun a => if x = a then (1:ℝ) else 0) := by
    rw [show (fun e : Fin n × Fin n => if x = e.1 then (1:ℝ) else 0)
        = (fun a => if x = a then (1:ℝ) else 0) ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp : l.length ≤ (l.rotate 1).length)]
  have h2 : (l.zip (l.rotate 1)).map (fun e => if x = e.2 then (1:ℝ) else 0)
      = (l.rotate 1).map (fun a => if x = a then (1:ℝ) else 0) := by
    rw [show (fun e : Fin n × Fin n => if x = e.2 then (1:ℝ) else 0)
        = (fun a => if x = a then (1:ℝ) else 0) ∘ Prod.snd from rfl, ← List.map_map,
      List.map_snd_zip (by simp : (l.rotate 1).length ≤ l.length)]
  rw [h1, h2, ((List.rotate_perm l 1).map _).sum_eq, sub_self]

theorem dEnergy_single (I : Instance n W) (f : Assignment n) (a : ℝ) (p q : Fin n) :
    dEnergy I f (fun x y => if x = p then (if y = q then a else 0) else 0) =
      if capNat I p q = 0 then 0 else f p q / (capNat I p q : ℝ) * a := by
  unfold dEnergy
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  · intro x _ hx; simp [hx]
  · simp

theorem dEnergy_move (I : Instance n W) {f : Assignment n} (hf : CapacityFeasible I f)
    {u v : Fin n} (h : ResArc I f u v) : dEnergy I f (move I f (u, v)) = resLen I f u v := by
  unfold move resLen
  by_cases hF : FwdP I f u v
  · simp only [hF, if_true]
    rw [dEnergy_single]
    obtain ⟨hlt, hle⟩ := hF
    have hc : (0:ℝ) < capNat I u v := lt_of_le_of_lt (hf u v).1 hlt
    have hc0 : capNat I u v ≠ 0 := by exact_mod_cast hc.ne'
    have hlt1 : f u v / (capNat I u v : ℝ) < 1 := by rw [div_lt_one hc]; exact hlt
    rw [if_neg hc0, if_pos hlt, mul_one]
    split_ifs with hb
    · exact (min_eq_left (hle hb)).symm
    · exact (min_eq_left hlt1.le).symm
  · simp only [hF, if_false]
    rw [dEnergy_single]
    have hb : 0 < f v u := by
      unfold FwdP at hF
      rcases h with h | h
      · by_contra hb; exact hF ⟨h, fun h' => absurd h' hb⟩
      · exact h
    have hc : (0:ℝ) < capNat I v u := lt_of_lt_of_le hb (hf v u).2
    have hc0 : capNat I v u ≠ 0 := by exact_mod_cast hc.ne'
    have hneg : -(f v u / (capNat I v u : ℝ)) ≤ 0 := by
      have := div_pos hb hc; linarith
    rw [if_neg hc0, if_pos hb]
    split_ifs with hf'
    · have : -(f v u / (capNat I v u : ℝ)) < f u v / (capNat I u v : ℝ) := by
        by_contra hcon; exact hF ⟨hf', fun _ => le_of_not_gt hcon⟩
      rw [min_eq_right this.le]; ring
    · rw [min_eq_right (by linarith)]; ring


theorem list_sum_nonpos (L : List ℝ) (h : ∀ x ∈ L, x ≤ 0) : L.sum ≤ 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.sum_cons]
    have := h a List.mem_cons_self
    have := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    linarith

theorem move_le_zero (I : Instance n W) (f : Assignment n) (e : Fin n × Fin n) {u v : Fin n}
    (hc : ¬ f u v < (capNat I u v : ℝ)) : move I f e u v ≤ 0 := by
  unfold move
  by_cases h1 : FwdP I f e.1 e.2
  · simp only [h1, if_true]
    split_ifs with hx hy
    · subst hx; subst hy; exact absurd h1.1 hc
    · exact le_rfl
    · exact le_rfl
  · simp only [h1, if_false]
    split_ifs <;> norm_num

theorem move_nonneg (I : Instance n W) (f : Assignment n) (e : Fin n × Fin n) {u v : Fin n}
    (hc : ¬ 0 < f u v) (hR : ResArc I f e.1 e.2) : 0 ≤ move I f e u v := by
  unfold move
  by_cases h1 : FwdP I f e.1 e.2
  · simp only [h1, if_true]
    split_ifs <;> norm_num
  · simp only [h1, if_false]
    split_ifs with hx hy
    · subst hx; subst hy
      exfalso
      unfold FwdP at h1
      rcases hR with h | h
      · exact h1 ⟨h, fun h' => absurd h' hc⟩
      · exact hc h
    · exact le_rfl
    · exact le_rfl

/-- Residual lengths are at least `-1` for a capacity-feasible assignment. -/
theorem resLen_ge_neg_one (I : Instance n W) {f : Assignment n} (hf : CapacityFeasible I f)
    {u v : Fin n} (h : ResArc I f u v) : -1 ≤ resLen I f u v := by
  unfold resLen
  refine le_min ?_ ?_
  · split_ifs
    · have := div_nonneg (hf u v).1 (Nat.cast_nonneg (α := ℝ) (capNat I u v)); linarith
    · norm_num
  · split_ifs with hb
    · have hc : (0:ℝ) < capNat I v u := lt_of_lt_of_le hb (hf v u).2
      have : f v u / (capNat I v u : ℝ) ≤ 1 := (div_le_one hc).2 (hf v u).2
      linarith
    · norm_num

theorem noNegCycle_of_minimizer (I : Instance n W) {s t : Fin n} (hst : s ≠ t) {p : ℝ}
    {f : Assignment n} (hf : IsFlow (network I) s t f p)
    (hmin : ∀ g, IsFlow (network I) s t g p → energy I f ≤ energy I g) :
    NoNegCycle (ResArc I f) (resLen I f) := by
  intro l ⟨_, _, hR⟩
  by_contra hneg
  push Not at hneg
  obtain ⟨_, hcf, hex⟩ := (RPBridge.isFlow_iff I hst f p).1 hf
  set D : Assignment n := fun a b => ((cycPairs l).map fun e => move I f e a b).sum with hD
  have hexD : ∀ x, excess D x = 0 := by
    intro x
    rw [hD, excess_listSum]
    simp only [excess_move]
    exact cyc_telescope l x
  have hpos : ∀ u v, 0 < D u v → f u v < (capNat I u v : ℝ) := by
    intro u v hDuv
    by_contra hc
    refine absurd hDuv (not_lt.2 (list_sum_nonpos _ ?_))
    intro z hz
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hz
    exact move_le_zero I f e hc
  have hneg' : ∀ u v, D u v < 0 → 0 < f u v := by
    intro u v hDuv
    by_contra hc
    refine absurd hDuv (not_lt.2 (List.sum_nonneg ?_))
    intro z hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
    exact move_nonneg I f e hc (hR e he)
  have hL : dEnergy I f D < 0 := by
    rw [hD, dEnergy_listSum]
    have : ((cycPairs l).map fun e => dEnergy I f (move I f e)) =
        (cycPairs l).map fun e => resLen I f e.1 e.2 :=
      List.map_congr_left fun e he => dEnergy_move I hcf (hR e he)
    rw [this]
    exact hneg
  obtain ⟨g, hcg, hexg, hlt⟩ := descent I hcf D hexD hpos hneg' hL
  have hg : IsFlow (network I) s t g p :=
    (RPBridge.isFlow_iff I hst g p).2
      ⟨RPBridge.supportedOnArcs_of_capacityFeasible I hcg, hcg, fun x => (hexg x).trans (hex x)⟩
  exact absurd (hmin g hg) (not_le.2 hlt)

end RPComp

/-! ===== RP_Potentials ===== -/

/-! # G3 — potentials from the absence of negative cycles (generic digraphs). Statement FIXED. -/

namespace RPComp
open scoped BigOperators

section PotentialsHelpers

variable {n : ℕ}

/-- Length of an (open) vertex path `w₀ → w₁ → ⋯ → w_k`. -/
noncomputable def pLen (ℓ : Fin n → Fin n → ℝ) : List (Fin n) → ℝ
  | a :: b :: t => ℓ a b + pLen ℓ (b :: t)
  | _ => 0

lemma pLen_eq_sum (ℓ : Fin n → Fin n → ℝ) :
    ∀ l : List (Fin n), pLen ℓ l = ((l.zip l.tail).map fun e => ℓ e.1 e.2).sum
  | [] => by simp [pLen]
  | [a] => by simp [pLen]
  | a :: b :: t => by
    rw [pLen, pLen_eq_sum ℓ (b :: t)]
    simp

lemma pLen_append_cons (ℓ : Fin n → Fin n → ℝ) (v : Fin n) (B : List (Fin n)) :
    ∀ A : List (Fin n), pLen ℓ (A ++ v :: B) = pLen ℓ (A ++ [v]) + pLen ℓ (v :: B)
  | [] => by simp [pLen]
  | [a] => by simp [pLen]
  | a :: b :: A => by
    have := pLen_append_cons ℓ v B (b :: A)
    simp only [List.cons_append] at this ⊢
    rw [pLen, pLen, this]; ring

lemma pLen_snoc (ℓ : Fin n → Fin n → ℝ) (p : List (Fin n)) (u v : Fin n) :
    pLen ℓ (p ++ [u] ++ [v]) = pLen ℓ (p ++ [u]) + ℓ u v := by
  rw [List.append_assoc, List.singleton_append, pLen_append_cons]
  simp [pLen]

lemma chain_zip {R : Fin n → Fin n → Prop} :
    ∀ l : List (Fin n), l.IsChain R → ∀ e ∈ l.zip l.tail, R e.1 e.2
  | [] => by simp
  | [a] => by simp
  | a :: b :: t => by
    intro h e he
    rw [List.isChain_cons_cons] at h
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact chain_zip (b :: t) h.2 e he

lemma pLen_lower {R : Fin n → Fin n → Prop} (ℓ : Fin n → Fin n → ℝ)
    (hR : ∀ u v, R u v → -1 ≤ ℓ u v) :
    ∀ (t : List (Fin n)) (a : Fin n), (a :: t).IsChain R → -(t.length : ℝ) ≤ pLen ℓ (a :: t)
  | [], a, _ => by simp [pLen]
  | b :: t, a, h => by
    rw [List.isChain_cons_cons] at h
    have ih := pLen_lower ℓ hR t b h.2
    have := hR a b h.1
    rw [pLen]; push_cast [List.length_cons]; linarith

/-- Simple `R`-paths ending at `v` (including the trivial path `[v]`). -/
def SPath (R : Fin n → Fin n → Prop) (v : Fin n) : Set (List (Fin n)) :=
  {p | p.Nodup ∧ p.IsChain R ∧ ∃ p', p = p' ++ [v]}

lemma cycle_of_path {R : Fin n → Fin n → Prop} (ℓ : Fin n → Fin n → ℝ) (v u : Fin n)
    (B C : List (Fin n)) (hc : (v :: B).Nodup) (hch : (v :: B).IsChain R)
    (hC : v :: B = C ++ [u]) (huv : R u v) :
    IsSimpleCycle R (v :: B) ∧ cycLen ℓ (v :: B) = pLen ℓ (v :: B) + ℓ u v := by
  have hrot : (v :: B).rotate 1 = B ++ [v] := by simp
  have hlen : (v :: B).length = (B ++ [v]).length := by simp
  have hzip : (v :: B ++ [v]).zip (v :: B ++ [v]).tail = cycPairs (v :: B) := by
    rw [cycPairs, hrot, List.cons_append, List.tail_cons, ← List.cons_append,
      ← List.append_nil (B ++ [v]), List.zip_append hlen]
    simp
  have hchain : (v :: B ++ [v]).IsChain R := by
    refine List.IsChain.append hch (by simp) ?_
    intro x hx y hy
    rw [hC] at hx
    simp at hx hy
    subst hx; subst hy; exact huv
  refine ⟨⟨by simp, hc, ?_⟩, ?_⟩
  · intro e he
    rw [← hzip] at he
    exact chain_zip _ hchain e he
  · rw [cycLen, ← hzip, ← pLen_eq_sum, hC, pLen_snoc]

lemma extend_path {R : Fin n → Fin n → Prop} (ℓ : Fin n → Fin n → ℝ) (h : NoNegCycle R ℓ)
    (u v : Fin n) (huv : R u v) (p : List (Fin n)) (hp : p ∈ SPath R u) :
    ∃ q ∈ SPath R v, pLen ℓ q ≤ pLen ℓ p + ℓ u v := by
  obtain ⟨hnd, hch, p', rfl⟩ := hp
  by_cases hv : v ∈ p' ++ [u]
  · obtain ⟨A, B, hAB⟩ := List.append_of_mem hv
    have hAB' : p' ++ [u] = (A ++ [v]) ++ B := by simp [hAB]
    refine ⟨A ++ [v], ⟨?_, ?_, A, rfl⟩, ?_⟩
    · rw [hAB'] at hnd; exact hnd.sublist (List.sublist_append_left _ _)
    · rw [hAB'] at hch; exact hch.left_of_append
    · have hnd2 : (v :: B).Nodup := by
        rw [hAB] at hnd; exact hnd.sublist (List.sublist_append_right _ _)
      have hch2 : (v :: B).IsChain R := by
        rw [hAB] at hch; exact hch.right_of_append
      obtain ⟨C, x, hCx⟩ : ∃ C x, v :: B = C ++ [x] := by
        rcases List.eq_nil_or_concat (v :: B) with h0 | ⟨C, x, hx⟩
        · simp at h0
        · exact ⟨C, x, by simpa using hx⟩
      have hxu : x = u := by
        have := congrArg List.getLast? hAB
        rw [hCx, ← List.append_assoc] at this
        simpa using this.symm
      subst hxu
      obtain ⟨hsc, hlen⟩ := cycle_of_path ℓ v x B C hnd2 hch2 hCx huv
      have h0 := h _ hsc
      rw [hAB, pLen_append_cons ℓ v B A]
      linarith
  · refine ⟨p' ++ [u] ++ [v], ⟨?_, ?_, _, rfl⟩, (pLen_snoc ℓ p' u v).le⟩
    · rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb; simp at hb; subst hb
      rintro rfl; exact hv ha
    · refine List.IsChain.append hch (by simp) ?_
      intro x hx y hy; simp at hx hy; subst hx; subst hy; exact huv

end PotentialsHelpers

/-- If every edge has length `≥ -1` and no simple cycle is negative, there are potentials in
`[0, n-1]` satisfying every edge constraint `π v ≤ π u + ℓ u v` (shortest simple paths from a
virtual root joined to every vertex by a 0-edge, shifted by `n - 1`). -/
theorem potentials_of_noNegCycle {n : ℕ} (R : Fin n → Fin n → Prop) (ℓ : Fin n → Fin n → ℝ)
    (hR : ∀ u v, R u v → -1 ≤ ℓ u v) (h : NoNegCycle R ℓ) :
    ∃ π : Fin n → ℝ, (∀ u v, R u v → π v ≤ π u + ℓ u v) ∧
      ∀ v, 0 ≤ π v ∧ π v ≤ (n : ℝ) - 1 := by
  set d : Fin n → ℝ := fun v => sInf (pLen ℓ '' SPath R v) with hd
  have hne : ∀ v, (pLen ℓ '' SPath R v).Nonempty := fun v =>
    ⟨_, [v], ⟨by simp, by simp, [], rfl⟩, rfl⟩
  have hlow : ∀ v, ∀ x ∈ pLen ℓ '' SPath R v, -((n : ℝ) - 1) ≤ x := by
    rintro v _ ⟨p, ⟨hnd, hch, p', rfl⟩, rfl⟩
    cases p' with
    | nil =>
      have : (1 : ℝ) ≤ n := by
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (fun h0 => by subst h0; exact v.elim0)
        exact_mod_cast this
      simp [pLen]; exact_mod_cast this
    | cons a t =>
      have h1 := pLen_lower ℓ hR (t ++ [v]) a hch
      have h2 := hnd.length_le_card
      simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil,
        Fintype.card_fin] at h2 h1 ⊢
      have : ((t.length + 1 : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
        have : t.length + 1 + 1 ≤ n := h2
        have : ((t.length + 1 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
        push_cast at this ⊢; linarith
      push_cast at h1 this; linarith
  have hbdd : ∀ v, BddBelow (pLen ℓ '' SPath R v) := fun v => ⟨_, hlow v⟩
  refine ⟨fun v => d v + ((n : ℝ) - 1), ?_, ?_⟩
  · intro u v huv
    have : d v - ℓ u v ≤ d u := by
      apply le_csInf (hne u)
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hle⟩ := extend_path ℓ h u v huv p hp
      have := csInf_le (hbdd v) ⟨q, hq, rfl⟩
      simp only [hd]; linarith
    simp only; linarith
  · intro v
    have h1 : d v ≤ 0 := by
      have := csInf_le (hbdd v) ⟨[v], ⟨by simp, by simp, [], rfl⟩, rfl⟩
      simpa [pLen] using this
    have h2 : -((n : ℝ) - 1) ≤ d v := le_csInf (hne v) (hlow v)
    constructor <;> simp only <;> linarith

end RPComp

/-! ===== RP_Complete ===== -/

/-! # G4 — clipped-potential representation, band shift, rounding: completeness.
Statements FIXED. While G1–G3 are in progress this imports frozen `_Stub` copies. -/

namespace RPComp
open RoundedPotentials.Main FlowsNetworks.MaxFlow
open scoped BigOperators

variable {n W : ℕ}

theorem capSum_zero_of_not_mem (l : List (Fin n × Fin n × ℕ)) (u v : Fin n)
    (h : (u, v) ∉ l.map (fun e => (e.1, e.2.1))) :
    (l.map (fun e => if e.1 = u ∧ e.2.1 = v then e.2.2 else 0)).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  split_ifs with h1
  · exact absurd (List.mem_map.2 ⟨e, he, Prod.ext h1.1 h1.2⟩) h
  · rfl

theorem capSum_le (l : List (Fin n × Fin n × ℕ)) (hnd : (l.map (fun e => (e.1, e.2.1))).Nodup)
    (hb : ∀ e ∈ l, e.2.2 ≤ W) (u v : Fin n) :
    (l.map (fun e => if e.1 = u ∧ e.2.1 = v then e.2.2 else 0)).sum ≤ W := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    split_ifs with h1
    · have hz : (u, v) ∉ l.map (fun e => (e.1, e.2.1)) := by
        obtain ⟨h1a, h1b⟩ := h1
        subst h1a h1b
        exact hnd.1
      rw [capSum_zero_of_not_mem l u v hz, add_zero]
      exact hb e (by simp)
    · rw [zero_add]
      exact ih hnd.2 (fun e' he' => hb e' (by simp [he']))

theorem clip_lip (a b : ℝ) : |clip a - clip b| ≤ |a - b| := by
  unfold clip
  rw [abs_le]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
  rcases le_total a 1 with ha1 | ha1 <;> rcases le_total b 1 with hb1 | hb1 <;>
  simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, ha, hb, ha1, hb1,
    zero_le_one] <;>
  constructor <;> cases abs_cases (a - b) <;> linarith

theorem clip_of_mem {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : clip z = z := by
  unfold clip; rw [max_eq_right h0, min_eq_right h1]

theorem n_pos_of (s : Fin n) : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact s.elim0)

/-- With `uniquePairs`, each pair carries at most one edge, so `capNat ≤ W`. -/
theorem capNat_le (I : Instance n W) (u v : Fin n) : capNat I u v ≤ W :=
  capSum_le I.edges I.uniquePairs I.bounded u v

/-- Every flow value is at most `(n - 1) W`. -/
theorem flowValue_le (I : Instance n W) {s t : Fin n} (hst : s ≠ t) {f : Assignment n} {w : ℝ}
    (hf : IsFlow (network I) s t f w) : w ≤ ((n : ℝ) - 1) * W := by
  obtain ⟨-, hcf, hex⟩ := (RPBridge.isFlow_iff I hst f w).1 hf
  have hs : excess f s = w := by rw [hex s]; simp [target, hst]
  have hss : f s s = 0 := by
    have h0 := hcf s s
    rw [RPBridge.capNat_eq_zero_of_not_mem I (fun h => (network I).loopless _ h rfl)] at h0
    simp at h0; linarith
  have hin : 0 ≤ ∑ u, f u s := Finset.sum_nonneg (fun u _ => (hcf u s).1)
  have hout : ∑ u, f s u ≤ ((n : ℝ) - 1) * W := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hss, zero_add]
    calc ∑ u ∈ Finset.univ.erase s, f s u ≤ ∑ u ∈ Finset.univ.erase s, (W : ℝ) :=
          Finset.sum_le_sum (fun u _ => (hcf s u).2.trans (by exact_mod_cast capNat_le I s u))
      _ = ((n : ℝ) - 1) * W := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (n_pos_of s)]
          simp
  unfold excess at hs
  linarith

/-- Lemma 3.4 (clipped-potential representation): some flow of value `p` has the form
`c_uv · clip(y_u − y_v)` with potentials in `[0, n − 1]`. -/
theorem clipped_rep (I : Instance n W) {s t : Fin n} (hst : s ≠ t) {p : ℝ}
    (hex : ∃ f, IsFlow (network I) s t f p) :
    ∃ (f : Assignment n) (y : Fin n → ℝ), IsFlow (network I) s t f p ∧
      (∀ v, 0 ≤ y v ∧ y v ≤ (n : ℝ) - 1) ∧
      ∀ u v, f u v = (capNat I u v : ℝ) * clip (y u - y v) := by
  obtain ⟨f, hf, hmin⟩ := exists_min_energy I hst hex
  have hneg := noNegCycle_of_minimizer I hst hf hmin
  have hcf : CapacityFeasible I f := ((RPBridge.isFlow_iff I hst f p).1 hf).2.1
  obtain ⟨π, hπ, hπb⟩ := potentials_of_noNegCycle (ResArc I f) (resLen I f)
    (fun u v h => resLen_ge_neg_one I hcf h) hneg
  refine ⟨f, fun v => (n : ℝ) - 1 - π v, hf, fun v => ⟨by linarith [hπb v], by linarith [hπb v]⟩,
    fun u v => ?_⟩
  obtain ⟨h0, h1⟩ := hcf u v
  set c : ℝ := (capNat I u v : ℝ) with hc
  have hfwd : f u v < c → π v - π u ≤ f u v / c := by
    intro hlt
    have := hπ u v (Or.inl hlt)
    have hl : resLen I f u v ≤ f u v / c := by
      unfold resLen; rw [if_pos hlt]; exact min_le_left _ _
    linarith
  have hbwd : 0 < f u v → f u v / c ≤ π v - π u := by
    intro hpos
    have := hπ v u (Or.inr hpos)
    have hl : resLen I f v u ≤ -(f u v / c) := by
      unfold resLen; rw [if_pos hpos]; exact min_le_right _ _
    linarith
  have hyd : (n : ℝ) - 1 - π u - ((n : ℝ) - 1 - π v) = π v - π u := by ring
  rw [hyd]
  rcases eq_or_lt_of_le (Nat.cast_nonneg (capNat I u v) : (0 : ℝ) ≤ c) with hc0 | hcpos
  · have hc' : c = 0 := by rw [hc]; exact hc0.symm
    rw [hc'] at h1 ⊢; rw [zero_mul]; linarith
  rcases eq_or_lt_of_le h0 with hf0 | hfpos
  · rw [← hf0] at hfwd ⊢
    rw [RPBridge.clip_of_nonpos (by simpa using hfwd hcpos), mul_zero]
  rcases eq_or_lt_of_le h1 with hfc | hfc
  · have := hbwd hfpos
    rw [hfc, div_self hcpos.ne'] at this
    rw [RPBridge.clip_of_one_le this, mul_one, hfc]
  · have e1 := hfwd hfc
    have e2 := hbwd hfpos
    have he : π v - π u = f u v / c := le_antisymm e1 e2
    rw [he, clip_of_mem (div_nonneg h0 hcpos.le) ((div_le_one hcpos).2 h1)]
    rw [mul_comm, div_mul_cancel₀ _ hcpos.ne']

/-- Lemma 3.5 / Corollary 3.6 (completeness): if the max flow is `p`, rounded grid potentials
with denominator `Q₀ = 32 n² W` pass the interval and excess checks. -/
theorem completeness (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t) (p : ℤ)
    (hmax : MaxValue I s t (p : ℝ)) :
    ∃ i : Fin n → ℤ, IndexRange n W i ∧ CertificateChecks I n s t p (gridPotential n W i) := by
  have hn : 0 < n := n_pos_of s
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hWR : (1 : ℝ) ≤ W := by exact_mod_cast hW
  -- max flow = min cut
  obtain ⟨v₀, hgr, hlst⟩ := max_flow_min_cut (network I) s t hst
  have hv : v₀ = (p : ℝ) := hgr.unique hmax
  obtain ⟨X, hsX, htX, hcapX⟩ := hlst.1
  obtain ⟨f, y, hf, hy, hrep⟩ := clipped_rep I hst hmax.1
  obtain ⟨hsup, hcf, hexc⟩ := (RPBridge.isFlow_iff I hst f p).1 hf
  have hsum := RPCut.sum_netFlowOut_of_conservation _ hst hf.2.2.2 hsX htX
  rw [RPCut.sum_netFlowOut] at hsum
  have hcut : arcSum (network I) (network I).cap X Xᶜ = p := by
    rw [← hv, hcapX]; rfl
  have hle : ∀ q ∈ arcsBetween (network I) X Xᶜ, f q.1 q.2 ≤ (network I).cap q.1 q.2 :=
    fun q _ => (hcf q.1 q.2).2
  have hnn : ∀ q ∈ arcsBetween (network I) Xᶜ X, 0 ≤ f q.1 q.2 := fun q _ => (hcf q.1 q.2).1
  have A1 : arcSum (network I) f X Xᶜ ≤ arcSum (network I) (network I).cap X Xᶜ :=
    Finset.sum_le_sum hle
  have A2 : 0 ≤ arcSum (network I) f Xᶜ X := Finset.sum_nonneg hnn
  have hsat := (Finset.sum_eq_sum_iff_of_le hle).1 (show arcSum (network I) f X Xᶜ =
    arcSum (network I) (network I).cap X Xᶜ by linarith)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (show arcSum (network I) f Xᶜ X = 0 by
    linarith)
  have hcr1 : ∀ u v, u ∈ X → v ∉ X → f u v = (capNat I u v : ℝ) := by
    intro u v hu hv'
    by_cases ha : (u, v) ∈ (network I).arcs
    · exact hsat (u, v) (Finset.mem_filter.2 ⟨ha, hu, Finset.mem_compl.2 hv'⟩)
    · rw [hsup u v ha, RPBridge.capNat_eq_zero_of_not_mem I ha]; simp
  have hcr2 : ∀ u v, u ∉ X → v ∈ X → f u v = 0 := by
    intro u v hu hv'
    by_cases ha : (u, v) ∈ (network I).arcs
    · exact hzero (u, v) (Finset.mem_filter.2 ⟨ha, Finset.mem_compl.2 hu, hv'⟩)
    · exact hsup u v ha
  -- band shift
  set y' : Fin n → ℝ := fun v => y v + if v ∈ X then (n : ℝ) else 0 with hy'
  have hrep' : ∀ u v, f u v = (capNat I u v : ℝ) * clip (y' u - y' v) := by
    intro u v
    have hu0 := hy u; have hv0 := hy v
    by_cases hu : u ∈ X <;> by_cases hv' : v ∈ X
    · rw [hrep u v]; simp only [hy', if_pos hu, if_pos hv']; congr 2; ring
    · rw [hcr1 u v hu hv', RPBridge.clip_of_one_le, mul_one]
      simp only [hy', if_pos hu, if_neg hv']; linarith
    · rw [hcr2 u v hu hv', RPBridge.clip_of_nonpos, mul_zero]
      simp only [hy', if_neg hu, if_pos hv']; linarith
    · rw [hrep u v]; simp only [hy', if_neg hu, if_neg hv']; congr 2; ring
  have hy'0 : ∀ v, 0 ≤ y' v := by
    intro v; simp only [hy']; split_ifs <;> linarith [(hy v).1]
  have hy'1 : ∀ v, y' v ≤ 2 * (n : ℝ) - 1 := by
    intro v; simp only [hy']; split_ifs <;> linarith [(hy v).2]
  -- rounding
  set Q : ℝ := (denominator n W : ℝ) with hQ
  have hQv : Q = 32 * n * n * W := by rw [hQ]; unfold denominator; push_cast; ring
  have hQpos : 0 < Q := by rw [hQv]; positivity
  refine ⟨fun v => ⌊Q * y' v⌋, ?_, ?_⟩
  · intro v
    refine ⟨Int.floor_nonneg.2 (mul_nonneg hQpos.le (hy'0 v)), ?_⟩
    have h1 : ((⌊Q * y' v⌋ : ℤ) : ℝ) ≤ Q * y' v := Int.floor_le _
    have h2 : Q * y' v ≤ Q * (2 * (n : ℝ) - 1) := mul_le_mul_of_nonneg_left (hy'1 v) hQpos.le
    have : ((⌊Q * y' v⌋ : ℤ) : ℝ) ≤ (((2 * (n : ℤ) - 1) * (denominator n W : ℤ) : ℤ) : ℝ) := by
      push_cast; rw [← hQ]; linarith
    exact_mod_cast this
  have hg : ∀ v, gridPotential n W (fun v => ⌊Q * y' v⌋) v ≤ y' v ∧
      y' v < gridPotential n W (fun v => ⌊Q * y' v⌋) v + 1 / Q := by
    intro v
    unfold gridPotential
    rw [← hQ]
    have h1 : ((⌊Q * y' v⌋ : ℤ) : ℝ) ≤ Q * y' v := Int.floor_le _
    have h2 : Q * y' v < ((⌊Q * y' v⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · rw [div_le_iff₀ hQpos]; linarith
    · rw [← add_div, lt_div_iff₀ hQpos]; linarith
  set g := gridPotential n W (fun v => ⌊Q * y' v⌋) with hgdef
  have hgX : ∀ v ∈ X, (n : ℝ) ≤ g v := by
    intro v hv'
    have hyv : y' v = y v + n := by simp only [hy', if_pos hv']
    have h3 : (((n : ℤ) * (denominator n W : ℤ) : ℤ) : ℝ) ≤ Q * y' v := by
      push_cast; rw [← hQ, hyv]; nlinarith [(hy v).1]
    have h4 := Int.le_floor.2 h3
    have h5 : ((n : ℤ) * (denominator n W : ℤ) : ℝ) ≤ ((⌊Q * y' v⌋ : ℤ) : ℝ) := by
      exact_mod_cast h4
    rw [hgdef]; unfold gridPotential; rw [← hQ, le_div_iff₀ hQpos]
    push_cast at h5; rw [← hQ] at h5; linarith
  have hgnX : ∀ v ∉ X, 0 ≤ g v ∧ g v ≤ (n : ℝ) - 1 := by
    intro v hv'
    have hyv : y' v = y v := by simp only [hy', if_neg hv', add_zero]
    refine ⟨?_, (hg v).1.trans (hyv ▸ (hy v).2)⟩
    rw [hgdef]; unfold gridPotential; rw [← hQ]
    have h0 := Int.floor_nonneg.2 (mul_nonneg hQpos.le (hy'0 v))
    exact div_nonneg (by exact_mod_cast h0) hQpos.le
  have hterm : ∀ a b, |induced I g a b - f a b| ≤ (W : ℝ) / Q := by
    intro a b
    have hdiff : |(g a - g b) - (y' a - y' b)| ≤ 1 / Q := by
      have := hg a; have := hg b
      rw [abs_le]; constructor <;> linarith
    rw [hrep' a b]; unfold induced
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (capNat I a b : ℝ) * |clip (g a - g b) - clip (y' a - y' b)|
        ≤ (capNat I a b : ℝ) * |(g a - g b) - (y' a - y' b)| :=
          mul_le_mul_of_nonneg_left (clip_lip _ _) (Nat.cast_nonneg _)
      _ ≤ (W : ℝ) * (1 / Q) :=
          mul_le_mul (by exact_mod_cast capNat_le I a b) hdiff (abs_nonneg _) (Nat.cast_nonneg _)
      _ = (W : ℝ) / Q := by ring
  refine ⟨⟨fun v => ?_, hgX s hsX, (hgnX t htX).2⟩, fun v => ?_⟩
  · by_cases hv' : v ∈ X
    · exact Or.inr ⟨hgX v hv', (hg v).1.trans (hy'1 v)⟩
    · exact Or.inl (hgnX v hv')
  · rw [← hexc v]
    unfold excess
    have hsplit : ((∑ u, induced I g v u) - ∑ u, induced I g u v) - ((∑ u, f v u) - ∑ u, f u v)
        = (∑ u, (induced I g v u - f v u)) - ∑ u, (induced I g u v - f u v) := by
      simp only [Finset.sum_sub_distrib]; ring
    rw [hsplit]
    calc |(∑ u, (induced I g v u - f v u)) - ∑ u, (induced I g u v - f u v)|
        ≤ |∑ u, (induced I g v u - f v u)| + |∑ u, (induced I g u v - f u v)| := abs_sub _ _
      _ ≤ (∑ u, |induced I g v u - f v u|) + ∑ u, |induced I g u v - f u v| :=
          add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (∑ _u : Fin n, (W : ℝ) / Q) + ∑ _u : Fin n, (W : ℝ) / Q :=
          add_le_add (Finset.sum_le_sum (fun u _ => hterm v u))
            (Finset.sum_le_sum (fun u _ => hterm u v))
      _ = 1 / (16 * (n : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hQv]; field_simp; ring
      _ ≤ epsilon n := by
          unfold epsilon
          exact one_div_le_one_div_of_le (by positivity) (by linarith)

end RPComp

/-! ===== RP_Prog ===== -/

/-! # Piece A (+ C) — what the verifier program computes. Statements FIXED. -/

namespace RPProg
open RoundedPotentials.Main
open scoped BigOperators

variable {n W : ℕ}

/-- The certificate list read as a vector of indices (the program's `indices.getD v 0`). -/
def certIdx (n : ℕ) (c : List ℤ) : Fin n → ℤ := fun v => c.getD v.val 0

theorem run_bind' {α β : Type} (m : StateM Meter α) (f : α → StateM Meter β) (st : Meter) :
    (m >>= f).run st = (f (m.run st).1).run (m.run st).2 := rfl
@[simp] theorem id_pure' {α : Type} (a : α) : (pure a : Id α) = a := rfl
@[simp] theorem run_pure' {α : Type} (a : α) (st : Meter) : (pure a : StateM Meter α).run st = (a, st) := rfl
@[simp] theorem isub_fst (a b : ℤ) (st) : ((isub a b).run st).1 = a - b := rfl
@[simp] theorem iadd_fst (a b : ℤ) (st) : ((iadd a b).run st).1 = a + b := rfl
@[simp] theorem imul_fst (a b : ℤ) (st) : ((imul a b).run st).1 = a * b := rfl
@[simp] theorem iabs_fst (a : ℤ) (st) : ((iabs a).run st).1 = |a| := rfl
@[simp] theorem ile_fst (a b : ℤ) (st) : ((ile a b).run st).1 = decide (a ≤ b) := rfl
@[simp] theorem inputRange_fst (a b : ℤ) (st) : ((inputRange a b).run st).1 = (decide (0 ≤ a) && decide (a ≤ b)) := rfl
theorem run_ite' {α : Type} (c : Prop) [Decidable c] (x y : StateM Meter α) (st) :
  (if c then x else y).run st = if c then x.run st else y.run st := by split <;> rfl

theorem ite_bool_cond {α : Type} (b : Bool) (inst : Decidable (b = true)) (x y : α) :
    @ite α (b = true) inst x y = bif b then x else y := by
  cases b <;> simp

theorem cond_run {α : Type} (b : Bool) (x y : StateM Meter α) (st : Meter) :
    (bif b then x else y).run st = bif b then x.run st else y.run st := by
  cases b <;> rfl

theorem iclip_fst (x q : ℤ) (st) : ((iclip x q).run st).1 =
    if q ≤ (if x ≤ 0 then 0 else x) then q else (if x ≤ 0 then 0 else x) := by
  simp only [iclip, run_bind', ile_fst, run_ite', run_pure', decide_eq_true_eq]
  split_ifs <;> simp_all

theorem readIndices_fst (bound : ℤ) : ∀ (l : List ℤ) (k : ℕ) (acc : Array ℤ) (st : Meter),
    ((readIndices k l acc bound).run st).1 =
      if l.length = k ∧ ∀ x ∈ l, 0 ≤ x ∧ x ≤ bound then some (acc ++ l.toArray) else none := by
  intro l
  induction l with
  | nil => intro k acc st; cases k <;> simp only [readIndices] <;> simp
  | cons x xs ih =>
    intro k acc st
    cases k with
    | zero => simp [readIndices]
    | succ k =>
      simp only [readIndices, run_bind', inputRange_fst]
      by_cases h : 0 ≤ x ∧ x ≤ bound
      · simp [h, ih]
      · simp only [Bool.and_eq_true, decide_eq_true_eq, run_ite']
        rw [if_neg h, if_neg (by simp only [List.length_cons, List.mem_cons, forall_eq_or_imp]; tauto)]
        rfl

theorem forIn_check_fst {α : Type} (l : List α) (P : α → Prop) [DecidablePred P]
    (f : α → Option Bool × Unit → StateM Meter (ForInStep (Option Bool × Unit)))
    (hf : ∀ x b st, ((f x b).run st).1 = if P x then .yield (none, ()) else .done (some false, ()))
    (st : Meter) :
    ((forIn l (none, ()) f).run st).1 = if ∀ x ∈ l, P x then (none, ()) else (some false, ()) := by
  induction l generalizing st with
  | nil => simp
  | cons x xs ih =>
    simp only [List.forIn_cons, run_bind', hf]
    by_cases h : P x
    · simp [h, ih]
    · simp [h]

theorem forIn_yield_fst {α β : Type} (l : List α) (step : α → β → β) (init : β)
    (f : α → β → StateM Meter (ForInStep β))
    (hf : ∀ x b st, ((f x b).run st).1 = .yield (step x b))
    (st : Meter) :
    ((forIn l init f).run st).1 = l.foldl (fun b x => step x b) init := by
  induction l generalizing st init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.forIn_cons, run_bind', hf]
    simp [ih]


theorem dec_fin {n : ℕ} (v s : Fin n) :
    (decide (((v:ℕ):ℤ) ≤ ((s:ℕ):ℤ)) && decide (((s:ℕ):ℤ) ≤ ((v:ℕ):ℤ))) = decide (v = s) := by
  rw [Bool.eq_iff_iff]; simp [Fin.ext_iff]; omega

def clipZ (x q : ℤ) : ℤ := if q ≤ (if x ≤ 0 then 0 else x) then q else (if x ≤ 0 then 0 else x)

def edgeStep {n : ℕ} (idx : Array ℤ) (q : ℤ) (e : Fin n × Fin n × ℕ) (cnt : Array ℤ) : Array ℤ :=
  let a := (e.2.2 : ℤ) * clipZ (idx.getD e.1.val 0 - idx.getD e.2.1.val 0) q
  let c1 := cnt.set! e.1.val (cnt.getD e.1.val 0 + a)
  c1.set! e.2.1.val (c1.getD e.2.1.val 0 - a)

theorem prog_fst {n W : ℕ} (I : Instance n W) (s t : Fin n) (p : ℤ) (c : List ℤ) (st : Meter) :
    ((verifyProgram I s t p c).run st).1 = true ↔
      (0 ≤ p ∧ p ≤ ((n:ℤ) - 1) * W) ∧
      (c.length = n ∧ ∀ x ∈ c, 0 ≤ x ∧ x ≤ (2 * (n:ℤ) - 1) * (32 * n * n * W)) ∧
      (∀ v : Fin n, c.toArray.getD v 0 ≤ ((n:ℤ) - 1) * (32 * n * n * W) ∨
          (n:ℤ) * (32 * n * n * W) ≤ c.toArray.getD v 0) ∧
      (n:ℤ) * (32 * n * n * W) ≤ c.toArray.getD s 0 ∧
      c.toArray.getD t 0 ≤ ((n:ℤ) - 1) * (32 * n * n * W) ∧
      ∀ v : Fin n,
        |(I.edges.foldl (fun b e => edgeStep c.toArray (32 * n * n * W) e b) (Array.replicate n 0)).getD v 0
          - (if v = s then 32 * n * n * W * p else if v = t then 0 - 32 * n * n * W * p else 0)|
          ≤ 4 * n * W := by
  dsimp only [verifyProgram, run_bind']
  simp only [ite_bool_cond, cond_run, isub_fst, imul_fst, inputRange_fst, Bool.cond_not]
  cases h1 : (decide (0 ≤ p) && decide (p ≤ ((n:ℤ) - 1) * W))
  · simp only [cond_false, run_pure']
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le] at h1
    constructor
    · intro h; cases h
    · intro h; omega
  simp only [cond_true]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  simp only [h1, true_and]
  dsimp only [run_bind']
  rw [readIndices_fst]
  by_cases h2 : c.length = n ∧ ∀ x ∈ c, 0 ≤ x ∧ x ≤ (2 * (n:ℤ) - 1) * (32 * n * n * W)
  swap
  · simp only [h2, if_false, false_and, iff_false]
    simp
  rw [if_pos h2]
  simp only [h2, true_and, Array.empty_append]
  dsimp only [run_bind']
  rw [forIn_check_fst (P := fun v : Fin n => c.toArray.getD v 0 ≤ ((n:ℤ) - 1) * (32 * n * n * W) ∨
          (n:ℤ) * (32 * n * n * W) ≤ c.toArray.getD v 0)]
  swap
  · intro x b st
    dsimp only [run_bind']
    simp only [ile_fst, cond_run, run_pure']
    generalize c.toArray.getD x 0 = a
    by_cases hA : a ≤ ((n:ℤ) - 1) * (32 * n * n * W) <;>
    by_cases hB : (n:ℤ) * (32 * n * n * W) ≤ a <;> simp [hA, hB]
  have hfin : ∀ (P : Fin n → Prop), (∀ x ∈ List.finRange n, P x) ↔ ∀ x, P x := by simp
  by_cases h3 : ∀ x : Fin n, c.toArray.getD x 0 ≤ ((n:ℤ) - 1) * (32 * n * n * W) ∨
          (n:ℤ) * (32 * n * n * W) ≤ c.toArray.getD x 0
  swap
  · rw [if_neg (by simpa using h3)]
    simp only [run_pure', h3, false_and, and_false, iff_false]
    simp
  rw [if_pos (by simpa using h3)]
  simp only [h3]
  dsimp only [run_bind']
  simp only [ile_fst, cond_run]
  by_cases h4 : (n:ℤ) * (32 * n * n * W) ≤ c.toArray.getD s 0
  swap
  · simp only [h4, decide_false, cond_false, run_pure', false_and, and_false, iff_false]
    simp
  simp only [h4, decide_true, cond_true, true_and]
  dsimp only [run_bind']
  simp only [ile_fst, cond_run]
  by_cases h5 : c.toArray.getD t 0 ≤ ((n:ℤ) - 1) * (32 * n * n * W)
  swap
  · simp only [h5, decide_false, cond_false, run_pure', false_and, and_false, iff_false]
    simp
  simp only [h5, decide_true, cond_true, true_and]
  dsimp only [run_bind']
  rw [forIn_yield_fst (step := edgeStep c.toArray (32 * n * n * W))]
  swap
  · intro e b st
    dsimp only [run_bind']
    simp only [isub_fst, iclip_fst, imul_fst, iadd_fst, run_pure']
    rfl
  simp only [imul_fst, isub_fst]
  rw [forIn_check_fst (P := fun v : Fin n =>
     |(I.edges.foldl (fun b e => edgeStep c.toArray (32 * n * n * W) e b) (Array.replicate n 0)).getD v 0
          - (if v = s then 32 * n * n * W * p else if v = t then 0 - 32 * n * n * W * p else 0)|
          ≤ 4 * n * W)]
  swap
  · intro v b st
    dsimp only [run_bind']
    simp only [ile_fst, isub_fst, iabs_fst, cond_run, run_pure', dec_fin, Bool.cond_decide]
    split_ifs with hX <;> simp [hX]
  split_ifs with h6
  · simp only [run_pure', true_iff]
    exact ⟨h2.2, fun _ => trivial, (hfin _).1 h6⟩
  · simp only [run_pure', Bool.false_eq_true, false_iff]
    exact fun h => h6 ((hfin _).2 h.2.2)

theorem getD_set! (a : Array ℤ) (i j : ℕ) (x : ℤ) (h : j < a.size) :
    (a.set! i x).getD j 0 = if i = j then x else a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all

theorem edgeStep_size {n : ℕ} (idx : Array ℤ) (q : ℤ) (e : Fin n × Fin n × ℕ) (b : Array ℤ) :
    (edgeStep idx q e b).size = b.size := by simp [edgeStep]

def amt {n : ℕ} (idx : Array ℤ) (q : ℤ) (e : Fin n × Fin n × ℕ) : ℤ :=
  (e.2.2 : ℤ) * clipZ (idx.getD e.1.val 0 - idx.getD e.2.1.val 0) q

theorem edgeStep_getD {n : ℕ} (idx : Array ℤ) (q : ℤ) (e : Fin n × Fin n × ℕ) (b : Array ℤ)
    (v : Fin n) (hb : b.size = n) :
    (edgeStep idx q e b).getD v 0 = b.getD v 0 + (if e.1 = v then amt idx q e else 0)
      - (if e.2.1 = v then amt idx q e else 0) := by
  simp only [edgeStep]
  rw [getD_set! _ _ _ _ (by simp; omega), getD_set! _ _ _ _ (by omega)]
  by_cases h1 : e.1 = v <;> by_cases h2 : e.2.1 = v <;>
    simp_all [Fin.ext_iff, amt]

theorem fold_getD {n : ℕ} (idx : Array ℤ) (q : ℤ) (v : Fin n) :
    ∀ (L : List (Fin n × Fin n × ℕ)) (acc : Array ℤ), acc.size = n →
    (L.foldl (fun b e => edgeStep idx q e b) acc).getD v 0 = acc.getD v 0
      + (L.map fun e => if e.1 = v then amt idx q e else 0).sum
      - (L.map fun e => if e.2.1 = v then amt idx q e else 0).sum := by
  intro L
  induction L with
  | nil => intro acc _; simp
  | cons e L ih =>
    intro acc hacc
    rw [List.foldl_cons, ih _ (by rw [edgeStep_size, hacc]), edgeStep_getD _ _ _ _ _ hacc]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem clipZ_eq (x q : ℤ) : clipZ x q = min q (max 0 x) := by
  unfold clipZ; split_ifs <;> omega

theorem clipZ_real (x q : ℤ) (hq : 0 < q) : (clipZ x q : ℝ) = q * clip (x / q) := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  rw [clipZ_eq, clip, mul_min_of_nonneg _ _ hq'.le, mul_max_of_nonneg _ _ hq'.le,
    mul_div_cancel₀ _ hq'.ne']
  push_cast; simp

def capL {n : ℕ} (L : List (Fin n × Fin n × ℕ)) (u v : Fin n) : ℕ :=
  (L.map (fun e => if e.1 = u ∧ e.2.1 = v then e.2.2 else 0)).sum

theorem out_sum {n : ℕ} (L : List (Fin n × Fin n × ℕ)) (v : Fin n) (g : Fin n → ℝ) :
    ∑ u, ((capL L v u : ℕ) : ℝ) * g u =
      (L.map fun e => if e.1 = v then (e.2.2 : ℝ) * g e.2.1 else 0).sum := by
  induction L with
  | nil => simp [capL]
  | cons e L ih =>
    have : ∀ u, capL (e :: L) v u = (if e.1 = v ∧ e.2.1 = u then e.2.2 else 0) + capL L v u := by
      intro u; simp [capL]
    simp only [this, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    by_cases h : e.1 = v <;> simp [h]

theorem in_sum {n : ℕ} (L : List (Fin n × Fin n × ℕ)) (v : Fin n) (g : Fin n → ℝ) :
    ∑ u, ((capL L u v : ℕ) : ℝ) * g u =
      (L.map fun e => if e.2.1 = v then (e.2.2 : ℝ) * g e.1 else 0).sum := by
  induction L with
  | nil => simp [capL]
  | cons e L ih =>
    have : ∀ u, capL (e :: L) u v = (if e.1 = u ∧ e.2.1 = v then e.2.2 else 0) + capL L u v := by
      intro u; simp [capL]
    simp only [this, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    by_cases h : e.2.1 = v <;> simp [h, and_comm]

/-- The flow counter equals `D · excess` of the induced assignment. -/
theorem counter_real {n W : ℕ} (I : Instance n W) (idx : Array ℤ) (D : ℤ) (hD : 0 < D) (v : Fin n) :
    ((((I.edges.map fun e => if e.1 = v then amt idx D e else 0).sum
      - (I.edges.map fun e => if e.2.1 = v then amt idx D e else 0).sum : ℤ)) : ℝ) =
      D * excess (induced I (fun u => (idx.getD u.val 0 : ℝ) / D)) v := by
  have hD' : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [excess, induced]
  have h1 := out_sum I.edges v (fun u => clip ((idx.getD v.val 0 : ℝ) / D - (idx.getD u.val 0 : ℝ) / D))
  have h2 := in_sum I.edges v (fun u => clip ((idx.getD u.val 0 : ℝ) / D - (idx.getD v.val 0 : ℝ) / D))
  simp only [capL] at h1 h2
  simp only [capNat, h1, h2, mul_sub, ← List.sum_map_mul_left]
  push_cast
  congr 1
  · congr 1; rw [List.map_map]; apply List.map_congr_left; intro e he
    by_cases h : e.1 = v
    · subst h; simp [amt, clipZ_real _ _ hD, sub_div]; ring
    · simp [h]
  · congr 1; rw [List.map_map]; apply List.map_congr_left; intro e he
    by_cases h : e.2.1 = v
    · subst h; simp [amt, clipZ_real _ _ hD, sub_div]; ring
    · simp [h]

theorem interval_iff (N : ℕ) (i D : ℤ) (hD : 0 < D) (h0 : 0 ≤ i) :
    (i ≤ ((N:ℤ)-1)*D ∨ (N:ℤ)*D ≤ i ∧ i ≤ (2*(N:ℤ)-1)*D) ↔
      ((0 ≤ (i:ℝ)/D ∧ (i:ℝ)/D ≤ (N:ℝ)-1) ∨ ((N:ℝ) ≤ (i:ℝ)/D ∧ (i:ℝ)/D ≤ 2*(N:ℝ)-1)) := by
  have hD' : (0:ℝ) < D := by exact_mod_cast hD
  rw [div_le_iff₀ hD', le_div_iff₀ hD', div_le_iff₀ hD', le_div_iff₀ hD']
  have hi : (0:ℝ) ≤ i := by exact_mod_cast h0
  have e1 : (i:ℝ) ≤ ((N:ℝ)-1)*D ↔ i ≤ ((N:ℤ)-1)*D := by
    rw [← Int.cast_le (R := ℝ)]; push_cast; rfl
  have e2 : (N:ℝ)*D ≤ i ↔ (N:ℤ)*D ≤ i := by
    rw [← Int.cast_le (R := ℝ)]; push_cast; rfl
  have e3 : (i:ℝ) ≤ (2*(N:ℝ)-1)*D ↔ i ≤ (2*(N:ℤ)-1)*D := by
    rw [← Int.cast_le (R := ℝ)]; push_cast; rfl
  rw [e1, e2, e3]
  simp [hi]

theorem le_divD (a i D : ℤ) (hD : 0 < D) : a * D ≤ i ↔ (a:ℝ) ≤ (i:ℝ)/D := by
  have hD' : (0:ℝ) < D := by exact_mod_cast hD
  rw [le_div_iff₀ hD', ← Int.cast_le (R := ℝ)]; push_cast; rfl

theorem divD_le (a i D : ℤ) (hD : 0 < D) : i ≤ a * D ↔ (i:ℝ)/D ≤ (a:ℝ) := by
  have hD' : (0:ℝ) < D := by exact_mod_cast hD
  rw [div_le_iff₀ hD', ← Int.cast_le (R := ℝ)]; push_cast; rfl


theorem arr_getD (c : List ℤ) (k : ℕ) : c.toArray.getD k 0 = c.getD k 0 := by simp

theorem replicate_getD (n k : ℕ) (h : k < n) : (Array.replicate n (0:ℤ)).getD k 0 = 0 := by simp [h]

theorem range_iff (c : List ℤ) (hlen : c.length = n) (P : ℤ → Prop) :
    (∀ x ∈ c, P x) ↔ ∀ v : Fin n, P (c.getD v.val 0) := by
  constructor
  · intro h v
    apply h
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := h ⟨k, by omega⟩
    rwa [List.getD_eq_getElem _ _ hk] at this

/-- The program's verdict, in arithmetic form (with `D = denominator n W`). -/
theorem prog_spec (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t) (p : ℤ) (c : List ℤ)
    (st : Meter) :
    ((verifyProgram I s t p c).run st).1 = true ↔
      (0 ≤ p ∧ p ≤ ((n : ℤ) - 1) * W) ∧ c.length = n ∧ IndexRange n W (certIdx n c) ∧
        CertificateChecks I n s t p (gridPotential n W (certIdx n c)) := by
  have hn : 0 < n := Fin.pos s
  set D : ℤ := (denominator n W : ℤ) with hDdef
  have hDeq : (32 * (n:ℤ) * n * W) = D := by simp [hDdef, denominator]
  have hD : 0 < D := by
    rw [← hDeq]
    have : (0:ℤ) < n := by exact_mod_cast hn
    have : (0:ℤ) < W := by exact_mod_cast hW
    positivity
  have hDR : ((D:ℤ):ℝ) = (denominator n W : ℝ) := by simp [hDdef]
  have hy : gridPotential n W (certIdx n c) = fun u => (c.toArray.getD u.val 0 : ℝ) / D := by
    funext u; simp [gridPotential, certIdx, hDR]
  -- counters
  have hcnt : ∀ v : Fin n,
      (((I.edges.foldl (fun b e => edgeStep c.toArray D e b) (Array.replicate n 0)).getD v 0 : ℤ) : ℝ)
        = D * excess (induced I (gridPotential n W (certIdx n c))) v := by
    intro v
    rw [fold_getD _ _ _ _ _ (by simp), replicate_getD _ _ v.isLt, zero_add, counter_real I _ D hD v, hy]
  have htg : ∀ v : Fin n,
      (((if v = s then D * p else if v = t then 0 - D * p else 0 : ℤ)) : ℝ) = D * target s t p v := by
    intro v
    by_cases h1 : v = s
    · subst h1; simp [target, hst]
    · by_cases h2 : v = t
      · subst h2; simp [target, h1]
      · simp [target, h1, h2]
  have heps : ((4 * (n:ℤ) * W : ℤ) : ℝ) = D * epsilon n := by
    rw [← hDeq, epsilon]
    have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast; field_simp; ring
  have herr : ∀ v : Fin n,
      |(I.edges.foldl (fun b e => edgeStep c.toArray D e b) (Array.replicate n 0)).getD v 0
          - (if v = s then D * p else if v = t then 0 - D * p else 0)| ≤ 4 * n * W ↔
      |excess (induced I (gridPotential n W (certIdx n c))) v - target s t p v| ≤ epsilon n := by
    intro v
    have hDr : (0:ℝ) < D := by exact_mod_cast hD
    rw [← Int.cast_le (R := ℝ), heps, Int.cast_abs, Int.cast_sub, hcnt v, htg v, ← mul_sub, abs_mul,
      abs_of_pos hDr, mul_le_mul_iff_right₀ hDr]
  rw [prog_fst, hDeq]
  simp only [CertificateChecks, Intervals, herr]
  rw [hy]
  simp only [IndexRange, certIdx, ← hDdef, arr_getD]
  have cN : ((n:ℤ):ℝ) = (n:ℝ) := Int.cast_natCast n
  have cN1 : (((n:ℤ) - 1 : ℤ):ℝ) = (n:ℝ) - 1 := by push_cast; rfl
  constructor
  · rintro ⟨hp, ⟨hlen, hr⟩, hb, hs, ht, he⟩
    have hr' := (range_iff c hlen _).1 hr
    refine ⟨hp, hlen, hr', ⟨fun v => ?_, ?_, ?_⟩, he⟩
    · refine (interval_iff n _ D hD (hr' v).1).1 ?_
      rcases hb v with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, (hr' v).2⟩
    · have := (le_divD n _ D hD).1 hs
      rwa [cN] at this
    · have := (divD_le ((n:ℤ) - 1) _ D hD).1 ht
      rwa [cN1] at this
  · rintro ⟨hp, hlen, hr', ⟨hb, hs, ht⟩, he⟩
    refine ⟨hp, ⟨hlen, (range_iff c hlen _).2 hr'⟩, fun v => ?_, ?_, ?_, he⟩
    · rcases (interval_iff n _ D hD (hr' v).1).2 (hb v) with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · rw [le_divD n _ D hD, cN]; exact hs
    · rw [divD_le ((n:ℤ) - 1) _ D hD, cN1]; exact ht


/-- Piece A: the verifier accepts exactly the specification. -/
theorem verify_true_iff (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t)
    (p : ℤ) (c : List ℤ) :
    (verify I s t p c).1 = true ↔
      (0 ≤ p ∧ p ≤ ((n : ℤ) - 1) * W) ∧ c.length = n ∧ IndexRange n W (certIdx n c) ∧
        CertificateChecks I n s t p (gridPotential n W (certIdx n c)) := by
  unfold verify
  exact prog_spec I hW hst p c _

theorem digits_bound (n W : ℕ) (hn : 1 ≤ n) (hW : 1 ≤ W) (i : ℤ) (h0 : 0 ≤ i)
    (h1 : i ≤ (2 * (n : ℤ) - 1) * (denominator n W : ℤ)) :
    binaryDigits i ≤ 3 * Nat.log 2 (n * W) + 10 := by
  unfold binaryDigits
  set L := Nat.log 2 (n * W)
  have hN : (i.natAbs : ℤ) = i := Int.natAbs_of_nonneg h0
  have hlt : i.natAbs < 64 * (n * W) ^ 3 := by
    have h1' : (i.natAbs : ℤ) ≤ (2 * (n : ℤ) - 1) * (32 * n * n * W) := by
      rw [hN]; simpa [denominator] using h1
    have hn' : (1:ℤ) ≤ n := by exact_mod_cast hn
    have hW' : (1:ℤ) ≤ W := by exact_mod_cast hW
    have : (2 * (n : ℤ) - 1) * (32 * n * n * W) < 64 * ((n:ℤ) * W) ^ 3 := by
      have hWW : (1:ℤ) ≤ (W:ℤ) * W := by nlinarith
      have hWc : (W:ℤ) ≤ (W:ℤ)^3 := by nlinarith
      have hn3 : (0:ℤ) < (n:ℤ)^3 := by positivity
      have hnn : (0:ℤ) < (n:ℤ) * n * W := by positivity
      nlinarith
    have : (i.natAbs : ℤ) < 64 * ((n:ℤ)*W)^3 := by linarith
    exact_mod_cast this
  have hpow : n * W < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (n * W) ^ 3 < (2 ^ (L + 1)) ^ 3 := Nat.pow_lt_pow_left hpow (by norm_num)
  have h4 : i.natAbs < 2 ^ (3 * L + 9) := by
    calc i.natAbs < 64 * (n * W) ^ 3 := hlt
      _ < 64 * (2 ^ (L + 1)) ^ 3 := by omega
      _ = 2 ^ (3 * L + 9) := by rw [← pow_mul]; rw [show 3 * L + 9 = 6 + (L + 1) * 3 by ring, pow_add]; norm_num
  by_cases hz : i.natAbs = 0
  · rw [hz]; simp
  · have := Nat.log_lt_of_lt_pow hz h4
    omega

/-- Piece C: part 1 of the goal theorem. -/
theorem part1 (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t)
    (p : ℤ) (c : List ℤ) (h : (verify I s t p c).1 = true) :
    c.length = n ∧ ∀ i ∈ c,
      0 ≤ i ∧ i ≤ (2 * (n : ℤ) - 1) * (denominator n W : ℤ) ∧
      binaryDigits i ≤ 3 * Nat.log 2 (n * W) + 10 := by
  obtain ⟨_, hlen, hr, _⟩ := (verify_true_iff I hW hst p c).1 h
  have hr' := (range_iff c hlen
    (fun x => 0 ≤ x ∧ x ≤ (2 * (n : ℤ) - 1) * (denominator n W : ℤ))).2 hr
  exact ⟨hlen, fun i hi => ⟨(hr' i hi).1, (hr' i hi).2,
    digits_bound n W (Fin.pos s) hW i (hr' i hi).1 (hr' i hi).2⟩⟩

end RPProg

/-! ===== RP_Meter ===== -/

/-! # Piece B: meter bounds (parts 3 and 4 of `RoundedPotentials.Main.theorem_1_1`). -/

namespace RPMeter
open RoundedPotentials.Main RPProg
open scoped BigOperators

variable {n W : ℕ}

/-- Hoare-style triple for the metered state monad: postcondition `Q` on the result,
at most `A` charged operations, and every newly recorded magnitude at most `M`. -/
def HT {α : Type} (M A : ℕ) (Q : α → Prop) (m : Counted α) : Prop :=
  ∀ st : Meter, Q (m.run st).1 ∧ (m.run st).2.ops ≤ st.ops + A ∧
    (m.run st).2.maxAbs ≤ max st.maxAbs M

theorem HT_pure {α : Type} {M A : ℕ} {Q : α → Prop} {a : α} (h : Q a) : HT M A Q (pure a) :=
  fun _ => ⟨h, Nat.le_add_right _ _, le_max_left _ _⟩

theorem HT_bind {α β : Type} {M A B : ℕ} {P : α → Prop} {Q : β → Prop} {m : Counted α}
    {f : α → Counted β} (hm : HT M A P m) (hf : ∀ a, P a → HT M B Q (f a)) :
    HT M (A + B) Q (m >>= f) := by
  intro st
  obtain ⟨h1, h2, h3⟩ := hm st
  obtain ⟨g1, g2, g3⟩ := hf _ h1 (m.run st).2
  rw [run_bind']
  exact ⟨g1, by omega, le_trans g3 (max_le h3 (le_max_right _ _))⟩

theorem HT_mono {α : Type} {M A A' : ℕ} {Q Q' : α → Prop} {m : Counted α}
    (h : HT M A Q m) (hA : A ≤ A') (hQ : ∀ a, Q a → Q' a) : HT M A' Q' m := by
  intro st
  obtain ⟨h1, h2, h3⟩ := h st
  exact ⟨hQ _ h1, by omega, h3⟩

theorem HT_ite {α : Type} {M A : ℕ} {Q : α → Prop} {c : Prop} {inst : Decidable c}
    {x y : Counted α} (h1 : c → HT M A Q x) (h2 : ¬c → HT M A Q y) :
    HT M A Q (@ite _ c inst x y) := by
  cases inst with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

theorem HT_ite_pure {α : Type} {M A : ℕ} {Q : α → Prop} {c : Prop} {inst : Decidable c}
    {a : α} {y : Counted α} (h : ¬c → HT M A Q y) (ha : Q a) :
    HT M A Q (@ite _ c inst (pure a) y) :=
  HT_ite (fun _ => HT_pure ha) h

theorem HT_charge {M : ℕ} {a b z : ℤ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hz : |z| ≤ M) :
    HT M 1 (fun _ => True) (charge a b z) := by
  intro st
  rw [Int.abs_eq_natAbs, Nat.cast_le] at ha hb hz
  refine ⟨trivial, le_refl _, ?_⟩
  show max st.maxAbs (max a.natAbs (max b.natAbs z.natAbs)) ≤ max st.maxAbs M
  omega

theorem HT_isub {M : ℕ} {a b : ℤ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hz : |a - b| ≤ M) :
    HT M 1 (fun r => r = a - b) (isub a b) :=
  HT_bind (B := 0) (HT_charge ha hb hz) (fun _ _ => HT_pure rfl)

theorem HT_iadd {M : ℕ} {a b : ℤ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hz : |a + b| ≤ M) :
    HT M 1 (fun r => r = a + b) (iadd a b) :=
  HT_bind (B := 0) (HT_charge ha hb hz) (fun _ _ => HT_pure rfl)

theorem HT_imul {M : ℕ} {a b : ℤ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hz : |a * b| ≤ M) :
    HT M 1 (fun r => r = a * b) (imul a b) :=
  HT_bind (B := 0) (HT_charge ha hb hz) (fun _ _ => HT_pure rfl)

theorem HT_iabs {M : ℕ} {a : ℤ} (ha : |a| ≤ M) :
    HT M 1 (fun r => r = |a|) (iabs a) :=
  HT_bind (B := 0) (HT_charge ha (by simp) (by simpa using ha)) (fun _ _ => HT_pure rfl)

theorem HT_ile {M : ℕ} {a b : ℤ} (hM : 1 ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    HT M 1 (fun r => r = decide (a ≤ b)) (ile a b) :=
  HT_bind (B := 0) (HT_charge ha hb (by split <;> simp <;> exact_mod_cast hM))
    (fun _ _ => HT_pure rfl)

theorem HT_inputRange {M : ℕ} {x b : ℤ} (hM : 1 ≤ M) (hb : |b| ≤ M) :
    HT M 2 (fun r => r = (decide (0 ≤ x) && decide (x ≤ b))) (inputRange x b) :=
  HT_bind (A := 1) (B := 1) (HT_charge (by simp) (by simp) (by split <;> simp <;> exact_mod_cast hM))
    (fun _ _ => HT_bind (B := 0) (HT_charge hb (by simp) (by split <;> simp <;> exact_mod_cast hM))
      (fun _ _ => HT_pure rfl))

theorem HT_iclip {M : ℕ} {x q : ℤ} (hM : 1 ≤ M) (hx : |x| ≤ M) (hq : |q| ≤ M) :
    HT M 2 (fun r => r = clipZ x q) (iclip x q) := by
  unfold iclip
  refine HT_bind (A := 1) (B := 1) (HT_ile hM hx (by simp)) (fun r1 h1 => ?_)
  dsimp only
  refine HT_ite (fun hc => ?_) (fun hc => ?_) <;> rw [pure_bind] <;>
    refine HT_bind (A := 1) (B := 0) (HT_ile hM hq ?_)
      (fun r2 h2 => HT_ite (fun h3 => HT_pure ?_) (fun h3 => HT_pure ?_)) <;>
    first
    | (simp; done)
    | assumption
    | (unfold clipZ; simp_all; done)
    | (unfold clipZ; simp_all; split_ifs <;> omega)

theorem HT_forIn {α β : Type} {M A : ℕ} (l : List α) (Inv : List α → β → Prop) (Fin' : β → Prop)
    (f : α → β → Counted (ForInStep β))
    (hf : ∀ pre x suf, pre ++ x :: suf = l → ∀ b, Inv pre b →
      HT M A (fun r => match r with
        | .yield b' => Inv (pre ++ [x]) b'
        | .done b' => Fin' b') (f x b))
    (hend : ∀ b, Inv l b → Fin' b) (init : β) (h0 : Inv [] init) :
    HT M (l.length * A) Fin' (forIn l init f) := by
  suffices H : ∀ suf pre, pre ++ suf = l → ∀ b, Inv pre b →
      HT M (suf.length * A) Fin' (forIn suf b f) from H l [] rfl init h0
  intro suf
  induction suf with
  | nil =>
    intro pre hpre b hb
    simp only [List.append_nil] at hpre
    subst hpre
    rw [List.forIn_nil]
    exact HT_pure (hend b hb)
  | cons x xs ih =>
    intro pre hpre b hb
    rw [List.forIn_cons]
    refine HT_mono (HT_bind (hf pre x xs hpre b hb) (fun r hr => ?_)) (A := A + xs.length * A)
      (by simp [Nat.succ_mul]; omega) (fun _ h => h)
    cases r with
    | done b' => exact HT_pure hr
    | yield b' => exact ih (pre ++ [x]) (by simp [hpre]) b' hr

theorem HT_read {M : ℕ} {bound : ℤ} (hM : 1 ≤ M) (hb : |bound| ≤ M) :
    ∀ (k : ℕ) (l : List ℤ) (acc : Array ℤ), (∀ x ∈ acc, 0 ≤ x ∧ x ≤ bound) →
    HT M (2 * k) (fun r => ∀ arr, r = some arr → ∀ x ∈ arr, 0 ≤ x ∧ x ≤ bound)
      (readIndices k l acc bound) := by
  intro k
  induction k with
  | zero =>
    intro l acc hacc
    cases l with
    | nil => exact HT_pure (by simpa using hacc)
    | cons x xs => exact HT_pure (by simp)
  | succ k ih =>
    intro l acc hacc
    cases l with
    | nil => exact HT_pure (by simp)
    | cons x xs =>
      simp only [readIndices]
      refine HT_mono (HT_bind (B := 2 * k) (HT_inputRange (x := x) hM hb) (fun r hr => ?_)) (by omega) (fun _ h => h)
      refine HT_ite (fun hc => ?_) (fun _ => HT_pure (by simp))
      apply ih
      subst hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      intro y hy
      rcases Array.mem_push.1 hy with h | h
      · exact hacc y h
      · subst h; exact hc

theorem getD_mem {arr : Array ℤ} {P : ℤ → Prop} (h : ∀ x ∈ arr, P x) (h0 : P 0) (i : ℕ) :
    P (arr.getD i 0) := by
  unfold Array.getD
  split
  · exact h _ (Array.getElem_mem _)
  · exact h0

theorem getD_set_cases (a : Array ℤ) (i j : ℕ) (x : ℤ) :
    (a.set! i x).getD j 0 = x ∨ (a.set! i x).getD j 0 = a.getD j 0 := by
  by_cases h : j < a.size
  · rw [getD_set! _ _ _ _ h]; split_ifs <;> simp
  · right; simp [Array.getD, h]

theorem sum_bound {α : Type} (L : List α) (P : α → Prop) [DecidablePred P] (f : α → ℤ) (B : ℤ)
    (h : ∀ e ∈ L, P e → 0 ≤ f e ∧ f e ≤ B) :
    0 ≤ (L.map fun e => if P e then f e else 0).sum ∧
      (L.map fun e => if P e then f e else 0).sum ≤ (L.filter P).length * B := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases hp : P e
    · have := h e (List.mem_cons_self) hp
      simp only [hp, if_true, decide_true, List.length_cons]
      push_cast
      constructor <;> linarith
    · simp only [hp, if_false, decide_false]
      simpa using ih'

theorem count_out {n : ℕ} (L : List (Fin n × Fin n × ℕ)) (hL : (L.map (fun e => (e.1, e.2.1))).Nodup)
    (v : Fin n) : (L.filter (fun e => e.1 = v)).length ≤ n := by
  set L' := L.filter (fun e => e.1 = v)
  have h1 : (L'.map (fun e => (e.1, e.2.1))).Nodup :=
    hL.sublist ((List.filter_sublist).map _)
  have h2 : ((L'.map (fun e => (e.1, e.2.1))).map Prod.snd).Nodup := by
    refine h1.map_on ?_
    intro x hx y hy hxy
    simp only [List.mem_map, L', List.mem_filter, decide_eq_true_eq] at hx hy
    obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hx
    obtain ⟨b, ⟨_, hb⟩, rfl⟩ := hy
    simp only at hxy
    simp [ha, hb, hxy]
  have := h2.length_le_card
  simpa using this

theorem count_in {n : ℕ} (L : List (Fin n × Fin n × ℕ)) (hL : (L.map (fun e => (e.1, e.2.1))).Nodup)
    (v : Fin n) : (L.filter (fun e => e.2.1 = v)).length ≤ n := by
  set L' := L.filter (fun e => e.2.1 = v)
  have h1 : (L'.map (fun e => (e.1, e.2.1))).Nodup :=
    hL.sublist ((List.filter_sublist).map _)
  have h2 : ((L'.map (fun e => (e.1, e.2.1))).map Prod.fst).Nodup := by
    refine h1.map_on ?_
    intro x hx y hy hxy
    simp only [List.mem_map, L', List.mem_filter, decide_eq_true_eq] at hx hy
    obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hx
    obtain ⟨b, ⟨_, hb⟩, rfl⟩ := hy
    simp only at hxy
    simp [ha, hb, hxy]
  have := h2.length_le_card
  simpa using this


theorem counter_bound {n W : ℕ} (I : Instance n W) (idx : Array ℤ) (Q : ℤ) (hQ : 0 ≤ Q)
    (pre suf : List (Fin n × Fin n × ℕ)) (h : pre ++ suf = I.edges) (v : Fin n) :
    -((n:ℤ) * (W * Q)) ≤ (pre.foldl (fun b e => edgeStep idx Q e b) (Array.replicate n 0)).getD v 0 ∧
    (pre.foldl (fun b e => edgeStep idx Q e b) (Array.replicate n 0)).getD v 0 ≤ (n:ℤ) * (W * Q) := by
  rw [fold_getD _ _ _ _ _ (by simp), replicate_getD _ _ v.isLt, zero_add]
  have hamt : ∀ e ∈ pre, 0 ≤ amt idx Q e ∧ amt idx Q e ≤ W * Q := by
    intro e he
    have hb : e.2.2 ≤ W := I.bounded e (h ▸ List.mem_append_left _ he)
    have hb' : ((e.2.2 : ℕ) : ℤ) ≤ W := by exact_mod_cast hb
    have hc := clipZ_eq (idx.getD e.1.val 0 - idx.getD e.2.1.val 0) Q
    have hc0 : 0 ≤ clipZ (idx.getD e.1.val 0 - idx.getD e.2.1.val 0) Q := by rw [hc]; omega
    have hc1 : clipZ (idx.getD e.1.val 0 - idx.getD e.2.1.val 0) Q ≤ Q := by rw [hc]; omega
    unfold amt
    exact ⟨by positivity, mul_le_mul hb' hc1 hc0 (by positivity)⟩
  have hnd : (pre.map (fun e => (e.1, e.2.1))).Nodup :=
    I.uniquePairs.sublist (h ▸ (List.sublist_append_left pre suf).map _)
  obtain ⟨a0, a1⟩ := sum_bound pre (fun e => e.1 = v) (amt idx Q) (W * Q) (fun e he _ => hamt e he)
  obtain ⟨b0, b1⟩ := sum_bound pre (fun e => e.2.1 = v) (amt idx Q) (W * Q) (fun e he _ => hamt e he)
  have c1 : (((pre.filter (fun e => e.1 = v)).length : ℕ) : ℤ) ≤ n := by exact_mod_cast count_out pre hnd v
  have c2 : (((pre.filter (fun e => e.2.1 = v)).length : ℕ) : ℤ) ≤ n := by exact_mod_cast count_in pre hnd v
  have hWQ : 0 ≤ (W:ℤ) * Q := by positivity
  have d1 := mul_le_mul_of_nonneg_right c1 hWQ
  have d2 := mul_le_mul_of_nonneg_right c2 hWQ
  constructor <;> linarith

theorem ops_arith (n m : ℕ) :
    1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
      (2 + (2 * n + ((List.finRange n).length * 2 + (1 + (1 + (m * 6 +
      (1 + (1 + ((List.finRange n).length * 7 + 0)))))))))))))))))))) ≤ 11 * n + 6 * m + 18 := by
  have := List.length_finRange (n := n)
  omega


set_option maxHeartbeats 1000000 in
theorem main_HT {n W : ℕ} (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t) (p : ℤ)
    (c : List ℤ) :
    HT (64 * n ^ 3 * W ^ 2) (11 * n + 6 * I.edges.length + 18) (fun _ => True)
      (verifyProgram I s t p c) := by
  have hn : 2 ≤ n := by
    have := s.isLt; have := t.isLt; have : s.val ≠ t.val := fun h => hst (Fin.ext h); omega
  have hM1 : 1 ≤ 64 * n ^ 3 * W ^ 2 := by
    have : 0 < 64 * n ^ 3 * W ^ 2 := by positivity
    omega
  have hx2 : (2:ℤ) ≤ n := by exact_mod_cast hn
  have hy1 : (1:ℤ) ≤ W := by exact_mod_cast hW
  have f1 : (n:ℤ) ≤ n * W := by nlinarith
  have f2 : (W:ℤ) ≤ n * W := by nlinarith
  have f3 : (n:ℤ) * W ≤ n * n * W := by nlinarith
  have f4 : (n:ℤ) * n ≤ n * n * W := by nlinarith
  have f5 : (n:ℤ) * n * W ≤ n * n * n * W := by nlinarith
  have f6 : (n:ℤ) * n * n * W ≤ n * n * n * W * W := by nlinarith
  have f7 : 2 * ((n:ℤ) * n * W * W) ≤ n * n * n * W * W := by nlinarith
  have f8 : 0 ≤ (n:ℤ) * n * W * W := by positivity
  have f9 : 0 ≤ (n:ℤ) * W := by positivity
  have f10 : 0 ≤ (n:ℤ) * n := by positivity
  have hQ0 : (0:ℤ) ≤ 32 * n * n * W := by positivity
  unfold verifyProgram
  dsimp only
  apply HT_mono (Q := fun _ => True) (A := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
    (2 + (2 * n + ((List.finRange n).length * 2 + (1 + (1 + (I.edges.length * 6 +
    (1 + (1 + ((List.finRange n).length * 7 + 0)))))))))))))))))))))
    ?main ?le (fun _ _ => trivial)
  case main =>
    apply HT_bind (HT_isub ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro nm h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro q1 h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro q2 h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro q h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro low h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro nq h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro tn h; subst h
    apply HT_bind (HT_isub ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro tnm h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro upper h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro pmax h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro tol1 h; subst h
    apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro tol h; subst h
    apply HT_bind (HT_inputRange hM1 ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro r h; subst h
    apply HT_ite (fun _ => HT_pure trivial); intro hc
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or,
      not_not] at hc
    obtain ⟨hp0, hp1⟩ := hc
    apply HT_bind (HT_read hM1 ?_ n c #[] (by simp)) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
    intro parsed hparsed
    rcases parsed with _ | indices
    swap
    · have hgd : ∀ i : ℕ, 0 ≤ indices.getD i 0 ∧
          indices.getD i 0 ≤ (2 * (n:ℤ) - 1) * (32 * n * n * W) :=
        fun i => getD_mem (P := fun x => 0 ≤ x ∧ x ≤ (2 * (n:ℤ) - 1) * (32 * n * n * W))
          (hparsed _ rfl) ⟨le_rfl, by nlinarith⟩ i
      dsimp only
      -- first loop
      apply HT_bind (HT_forIn (A := 2) (List.finRange n) (fun _ _ => True) (fun _ => True) _ ?body1
        (fun _ _ => trivial) _ trivial)
      case body1 =>
        intro pre v suf _ b _
        obtain ⟨g0, g1⟩ := hgd v.val
        refine HT_bind (B := 1) (HT_ile hM1 (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun r1 _ => ?_)
        refine HT_bind (B := 0) (HT_ile hM1 (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun r2 _ => ?_)
        exact HT_ite (fun _ => HT_pure trivial) (fun _ => HT_pure trivial)
      intro r _
      rcases r with ⟨_ | r, u⟩
      dsimp only
      obtain ⟨gs0, gs1⟩ := hgd s.val
      obtain ⟨gt0, gt1⟩ := hgd t.val
      apply HT_bind (HT_ile hM1 ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
      intro r h; subst h
      apply HT_ite_pure (ha := trivial); intro _
      apply HT_bind (HT_ile hM1 ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
      intro r h; subst h
      apply HT_ite_pure (ha := trivial); intro _
      -- edge loop
      apply HT_bind (HT_forIn (A := 6) I.edges
        (fun pre cnt => cnt = pre.foldl (fun b e => edgeStep indices (32 * n * n * W) e b)
          (Array.replicate n 0))
        (fun cnt => cnt = I.edges.foldl (fun b e => edgeStep indices (32 * n * n * W) e b)
          (Array.replicate n 0)) _ ?body2 (fun _ h => h) _ rfl)
      case body2 =>
        intro pre x suf hpre b hb
        obtain ⟨g0, g1⟩ := hgd x.1.val
        obtain ⟨g2, g3⟩ := hgd x.2.1.val
        obtain ⟨k0, k1⟩ := hb ▸ counter_bound I indices _ hQ0 pre (x :: suf) hpre x.1
        obtain ⟨k2, k3⟩ := hb ▸ counter_bound I indices _ hQ0 pre (x :: suf) hpre x.2.1
        have hx : x ∈ I.edges := hpre ▸ (by simp)
        have hw : ((x.2.2 : ℕ) : ℤ) ≤ W := by exact_mod_cast I.bounded x hx
        have hw0 : (0:ℤ) ≤ ((x.2.2 : ℕ) : ℤ) := by positivity
        refine HT_bind (B := 5) (HT_isub (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun drop hdrop => ?_)
        refine HT_bind (B := 3) (HT_iclip hM1 (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun cl hcl => ?_)
        have hc0 : 0 ≤ cl := by rw [hcl, clipZ_eq]; omega
        have hc1 : cl ≤ 32 * n * n * W := by rw [hcl, clipZ_eq]; omega
        have ha1 : ((x.2.2 : ℕ) : ℤ) * cl ≤ W * (32 * n * n * W) := mul_le_mul hw hc1 hc0 (by positivity)
        have ha0 : 0 ≤ ((x.2.2 : ℕ) : ℤ) * cl := mul_nonneg hw0 hc0
        refine HT_bind (B := 2) (HT_imul (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun am ham => ?_)
        refine HT_bind (B := 1) (HT_iadd (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun eu heu => ?_)
        have hc1w : -((n:ℤ) * (W * (32 * n * n * W))) - W * (32 * n * n * W) ≤
            (b.set! x.1.val eu).getD x.2.1.val 0 ∧
            (b.set! x.1.val eu).getD x.2.1.val 0 ≤
              (n:ℤ) * (W * (32 * n * n * W)) + W * (32 * n * n * W) := by
          rcases getD_set_cases b x.1.val x.2.1.val eu with h | h <;> rw [h] <;>
            constructor <;> linarith
        obtain ⟨k4, k5⟩ := hc1w
        refine HT_bind (B := 0) (HT_isub (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun ev hev => ?_)
        refine HT_pure ?_
        subst hev heu ham hcl hdrop hb
        rw [List.foldl_append]
        rfl
      intro cnt hcnt
      have hqp0 : 0 ≤ 32 * (n:ℤ) * n * W * p := mul_nonneg hQ0 hp0
      have hqp1 : 32 * (n:ℤ) * n * W * p ≤ 32 * (n:ℤ) * n * W * ((n - 1) * W) :=
        mul_le_mul_of_nonneg_left hp1 hQ0
      apply HT_bind (HT_imul ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
      intro qp h; subst h
      apply HT_bind (HT_isub ?_ ?_ ?_) <;> try (rw [abs_le]; push_cast; constructor <;> linarith)
      intro negqp h; subst h
      apply HT_bind (B := 0) (HT_forIn (A := 7) (List.finRange n) (fun _ _ => True) (fun _ => True) _ ?body3
        (fun _ _ => trivial) _ trivial)
      case body3 =>
        intro pre v suf _ b _
        have hv : ((v : ℕ) : ℤ) < n := by exact_mod_cast v.isLt
        have hs : ((s : ℕ) : ℤ) < n := by exact_mod_cast s.isLt
        have ht : ((t : ℕ) : ℤ) < n := by exact_mod_cast t.isLt
        have hv0 : (0:ℤ) ≤ ((v : ℕ) : ℤ) := by positivity
        have hs0 : (0:ℤ) ≤ ((s : ℕ) : ℤ) := by positivity
        have ht0 : (0:ℤ) ≤ ((t : ℕ) : ℤ) := by positivity
        obtain ⟨k0, k1⟩ := counter_bound I indices _ hQ0 I.edges [] (by simp) v
        rw [← hcnt] at k0 k1
        refine HT_bind (B := 6) (HT_ile hM1 (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun _ _ => ?_)
        refine HT_bind (B := 5) (HT_ile hM1 (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun _ _ => ?_)
        refine HT_bind (B := 4) (HT_ile hM1 (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun _ _ => ?_)
        refine HT_bind (B := 3) (HT_ile hM1 (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith))) (fun _ _ => ?_)
        refine HT_bind (B := 2) (HT_isub (by (rw [abs_le]; push_cast; constructor <;> linarith)) (by split_ifs <;> (rw [abs_le]; push_cast; constructor <;> linarith)) (by split_ifs <;> (rw [abs_le]; push_cast; constructor <;> linarith)))
          (fun err h => ?_)
        subst h
        refine HT_bind (B := 1) (HT_iabs (by split_ifs <;> (rw [abs_le]; push_cast; constructor <;> linarith))) (fun mg h => ?_)
        subst h
        refine HT_bind (B := 0) (HT_ile hM1 (by rw [abs_abs]; split_ifs <;> (rw [abs_le]; push_cast; constructor <;> linarith)) (by (rw [abs_le]; push_cast; constructor <;> linarith)))
          (fun _ _ => ?_)
        exact HT_ite (fun _ => HT_pure trivial) (fun _ => HT_pure trivial)
      intro r _
      rcases r with ⟨_ | r, u⟩ <;> exact HT_pure trivial
      exact HT_pure trivial
    · exact HT_pure trivial
  case le => exact ops_arith n I.edges.length


theorem log_bound (x n W : ℕ) (hx : x ≤ 64 * n ^ 3 * W ^ 2) (hW : 1 ≤ W) :
    Nat.log 2 x + 1 ≤ 3 * Nat.log 2 (n * W) + 10 := by
  set L := Nat.log 2 (n * W)
  have hpow : n * W < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (n * W) ^ 3 < (2 ^ (L + 1)) ^ 3 := Nat.pow_lt_pow_left hpow (by norm_num)
  have h4 : x < 2 ^ (3 * L + 9) := by
    calc x ≤ 64 * n ^ 3 * W ^ 2 := hx
      _ ≤ 64 * n ^ 3 * W ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (by norm_num))
      _ = 64 * (n * W) ^ 3 := by ring
      _ < 64 * (2 ^ (L + 1)) ^ 3 := by omega
      _ = 2 ^ (3 * L + 9) := by
        rw [← pow_mul, show 3 * L + 9 = 6 + (L + 1) * 3 by ring, pow_add]; norm_num
  by_cases hz : x = 0
  · subst hz; simp
  · have := Nat.log_lt_of_lt_pow hz h4
    omega

/-- Part 3 of the goal. -/
theorem part3 (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t) :
    ∀ (p : ℤ) (certificate : List ℤ),
      (verify I s t p certificate).2.ops ≤ 100 * (n + I.edges.length) + 100 := by
  intro p c
  have := (main_HT I hW hst p c ⟨0, 0⟩).2.1
  unfold verify
  simp only at this
  omega

/-- Part 4 of the goal. -/
theorem part4 (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t) :
    ∀ (p : ℤ) (certificate : List ℤ),
      (verify I s t p certificate).2.maxAbs ≤ 64 * n ^ 3 * W ^ 2 ∧
      Nat.log 2 ((verify I s t p certificate).2.maxAbs) + 1 ≤
        3 * Nat.log 2 (n * W) + 10 := by
  intro p c
  have h := (main_HT I hW hst p c ⟨0, 0⟩).2.2
  have h' : (verify I s t p c).2.maxAbs ≤ 64 * n ^ 3 * W ^ 2 := by
    unfold verify
    simpa using h
  exact ⟨h', log_bound _ n W h' hW⟩

end RPMeter

/-! ===== RP_Main12 ===== -/

/-! # Assembly of parts 1 and 2 of `RoundedPotentials.Main.theorem_1_1`. -/

namespace RPMain
open RoundedPotentials.Main FlowsNetworks.MaxFlow

variable {n W : ℕ}

theorem certIdx_ofFn (i : Fin n → ℤ) : RPProg.certIdx n (List.ofFn i) = i := by
  funext v
  simp [RPProg.certIdx, List.getD_eq_getElem?_getD]

/-- Part 1 of the goal. -/
theorem part1 (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t) :
    ∀ (p : ℤ) (certificate : List ℤ), (verify I s t p certificate).1 = true →
      certificate.length = n ∧ ∀ i ∈ certificate,
        0 ≤ i ∧ i ≤ (2 * (n : ℤ) - 1) * (denominator n W : ℤ) ∧
        binaryDigits i ≤ 3 * Nat.log 2 (n * W) + 10 :=
  fun p c h => RPProg.part1 I hW hst p c h

/-- Part 2 of the goal. -/
theorem part2 (I : Instance n W) (hW : 1 ≤ W) {s t : Fin n} (hst : s ≠ t) :
    ∀ p : ℤ, 0 ≤ p →
      ((∃ certificate : List ℤ, (verify I s t p certificate).1 = true) ↔
        MaxValue I s t (p : ℝ)) := by
  intro p hp
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨-, -, -, hchk⟩ := (RPProg.verify_true_iff I hW hst p c).1 hc
    exact RPSound.lemma_3_2 I hst le_rfl p _ hchk
  · intro hmax
    obtain ⟨i, hi, hchk⟩ := RPComp.completeness I hW hst p hmax
    obtain ⟨f, hf⟩ := hmax.1
    have hle := RPComp.flowValue_le I hst hf
    refine ⟨List.ofFn i, (RPProg.verify_true_iff I hW hst p _).2 ⟨⟨hp, ?_⟩, by simp, ?_, ?_⟩⟩
    · exact_mod_cast hle
    · rw [certIdx_ofFn]; exact hi
    · rw [certIdx_ofFn]; exact hchk

end RPMain

open RoundedPotentials.Main in
theorem solution {n W : ℕ} (I : Instance n W) (hW : 1 ≤ W)
    (s t : Fin n) (hst : s ≠ t) :
    (∀ (p : ℤ) (certificate : List ℤ), (verify I s t p certificate).1 = true →
      certificate.length = n ∧ ∀ i ∈ certificate,
        0 ≤ i ∧ i ≤ (2 * (n : ℤ) - 1) * (denominator n W : ℤ) ∧
        binaryDigits i ≤ 3 * Nat.log 2 (n * W) + 10) ∧
    (∀ p : ℤ, 0 ≤ p →
      ((∃ certificate : List ℤ, (verify I s t p certificate).1 = true) ↔
        MaxValue I s t (p : ℝ))) ∧
    (∀ (p : ℤ) (certificate : List ℤ),
      (verify I s t p certificate).2.ops ≤ 100 * (n + I.edges.length) + 100) ∧
    (∀ (p : ℤ) (certificate : List ℤ),
      (verify I s t p certificate).2.maxAbs ≤ 64 * n ^ 3 * W ^ 2 ∧
      Nat.log 2 ((verify I s t p certificate).2.maxAbs) + 1 ≤
        3 * Nat.log 2 (n * W) + 10) :=
  ⟨RPMain.part1 I hW hst, RPMain.part2 I hW hst,
   RPMeter.part3 I hW hst, RPMeter.part4 I hW hst⟩
