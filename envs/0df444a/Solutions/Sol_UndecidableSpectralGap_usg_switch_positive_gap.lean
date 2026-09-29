-- Prove2me | solution 1 for UndecidableSpectralGap.usg_switch_positive_gap
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:53:31.915601+00:00
-- url     : https://prove2.me/submissions/91a98387-3a04-4232-b27e-a656de0d1493

import Definitions.Def_usg_switch_entry_data
import Definitions.Def_usg_three_state_switch
set_option autoImplicit false
set_option maxHeartbeats 8000000
open UndecidableSpectralGap

namespace AgentBUSG

variable {L : ℕ}

theorem agree_eq_iff {p q : Site L} {c c' : Config L 3}
    (h : ∀ s, s ≠ p → s ≠ q → c s = c' s) :
    c = c' ↔ c p = c' p ∧ c q = c' q := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext s
    by_cases hp : s = p
    · subst hp; exact h1
    by_cases hq : s = q
    · subst hq; exact h2
    exact h s hp hq

theorem agree_swap_iff {p q : Site L} (hpq : p ≠ q) {c c' : Config L 3}
    (h : ∀ s, s ≠ p → s ≠ q → c s = c' s) :
    c' = c ∘ Equiv.swap p q ↔ c' p = c q ∧ c' q = c p := by
  constructor
  · rintro rfl
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rintro ⟨h1, h2⟩
    funext s
    by_cases hp : s = p
    · subst hp; simp [h1]
    by_cases hq : s = q
    · subst hq; simp [h2]
    simp [Equiv.swap_apply_of_ne_of_ne hp hq, h s hp hq]

theorem one_entry (p : Site L) (a : ℝ) (c c' : Config L 3) :
    embedOne p ((a : ℂ) • switchProjector) c c' =
      if c = c' then (if c p ≠ 0 then (a : ℂ) else 0) else 0 := by
  unfold embedOne
  by_cases hc : c = c'
  · subst hc; simp [switchProjector]
  · rw [if_neg hc]
    split_ifs with hag
    · have hne : c p ≠ c' p := by
        intro he; apply hc; funext s
        by_cases hs : s = p
        · subst hs; exact he
        · exact hag s hs
      simp [switchProjector, hne]
    · rfl

theorem guard_entry (e : Site L × Site L) (hne : e.1 ≠ e.2) (c c' : Config L 3) :
    embedTwo e.1 e.2 switchGuard c c' =
      if c = c' then (if switchBoundaryAt c e then (1 : ℂ) else 0) else 0 := by
  unfold embedTwo
  by_cases hc : c = c'
  · subst hc
    simp only [implies_true, if_true]
    unfold switchGuard
    by_cases hb : switchBoundaryAt c e
    · rw [if_pos hb, if_pos ⟨rfl, hb⟩]
    · rw [if_neg hb, if_neg (fun h => hb h.2)]
  · rw [if_neg hc]
    split_ifs with hag
    · have := (agree_eq_iff hag).not.mp hc
      unfold switchGuard
      rw [if_neg]
      rintro ⟨h1, -⟩
      simp only [Prod.mk.injEq] at h1
      exact this h1
    · rfl

theorem exch_entry (e : Site L × Site L) (hne : e.1 ≠ e.2) (c c' : Config L 3) :
    embedTwo e.1 e.2 switchExchange c c' =
      if c = c' then (if c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 then (1 : ℂ) else 0)
      else (if c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧ c' = c ∘ Equiv.swap e.1 e.2
        then (-1 : ℂ) else 0) := by
  unfold embedTwo
  by_cases hag : ∀ s, s ≠ e.1 → s ≠ e.2 → c s = c' s
  · rw [if_pos hag]
    simp only [agree_eq_iff hag, agree_swap_iff hne hag]
    generalize c e.1 = x1, c e.2 = x2, c' e.1 = y1, c' e.2 = y2
    fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
      simp [switchExchange, switchVector]
  · rw [if_neg hag]
    have h1 : c ≠ c' := by rintro rfl; exact hag (fun _ _ _ => rfl)
    rw [if_neg h1, if_neg]
    rintro ⟨-, -, -, hsw⟩
    apply hag
    intro s hs1 hs2
    rw [hsw]
    simp [Equiv.swap_apply_of_ne_of_ne hs1 hs2]

theorem lin_entry (p q : Site L) (b : ℝ) (c c' : Config L 3) :
    embedTwo p q (switchGuard + (b : ℂ) • switchExchange) c c' =
      embedTwo p q switchGuard c c' + (b : ℂ) * embedTwo p q switchExchange c c' := by
  unfold embedTwo
  split_ifs <;> simp [Matrix.add_apply, Matrix.smul_apply]

theorem row_ne {e : Site L × Site L} (he : e ∈ rowEdges L) : e.1 ≠ e.2 := by
  intro h
  simp only [rowEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [h] at he
  omega

theorem col_ne {e : Site L × Site L} (he : e ∈ colEdges L) : e.1 ≠ e.2 := by
  intro h
  simp only [colEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [h] at he
  omega

theorem sum_ite_const {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (x : ℂ) :
    (∑ i ∈ s, if P i then x else 0) = x * ((s.filter P).card : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem rate_sum (b : ℝ) (c : Config L 3) :
    ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j =
      b * (((rowEdges L).filter (fun e => c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2)).card : ℝ) := by
  unfold switchTransitionRate
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hD : c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2
  · have hne : c ∘ Equiv.swap e.1 e.2 ≠ c := by
      intro h
      have := congrFun h e.1
      simp [Equiv.swap_apply_left] at this
      exact hD.2.2 this.symm
    have hiff : ∀ x : Config L 3, (c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) ↔ x = c ∘ Equiv.swap e.1 e.2 :=
      fun x => ⟨fun h => h.2.2.2, fun h => ⟨hD.1, hD.2.1, hD.2.2, h⟩⟩
    simp only [hiff]
    rw [Finset.sum_ite_eq']
    simp [hne]
    exact hD
  · have hf : ∀ x : Config L 3, ¬(c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) := fun x h => hD ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [hf, hD, if_false, Finset.sum_const_zero]

end AgentBUSG

namespace AgentBUSG
theorem entry
    (L : ℕ) (a b : ℝ) (c c' : Config L 3) :
    switchHam L a b c c' =
      if c = c' then
        ((switchPotential L a c +
          ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j : ℝ) : ℂ)
      else -((switchTransitionRate L b c c' : ℝ) : ℂ) := by
  unfold switchHam latticeHam
  simp only [Matrix.add_apply, Matrix.sum_apply]
  rw [Finset.sum_congr rfl (fun e he => by
      rw [lin_entry, guard_entry e (row_ne he), exch_entry e (row_ne he)])]
  rw [Finset.sum_congr rfl (fun e he => guard_entry (L := L) e (col_ne he) c c')]
  simp only [one_entry]
  by_cases hc : c = c'
  · subst hc
    simp only [if_true]
    rw [rate_sum]
    unfold switchPotential switchBoundaryCount switchOccupiedCount
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, sum_ite_const, sum_ite_const, sum_ite_const, sum_ite_const]
    push_cast
    ring
  · simp only [if_neg hc, Finset.sum_const_zero, add_zero, zero_add]
    rw [← Finset.mul_sum, sum_ite_const]
    unfold switchTransitionRate
    push_cast
    ring


end AgentBUSG

namespace AgentBUSG
open UndecidableSpectralGap

variable {L : ℕ}

noncomputable def S (L : ℕ) (b : ℝ) (c : Config L 3) : ℝ :=
  ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j

theorem rate_nonneg {b : ℝ} (hb : 0 ≤ b) (c j : Config L 3) :
    0 ≤ switchTransitionRate L b c j := by
  unfold switchTransitionRate; positivity

theorem S_nonneg {b : ℝ} (hb : 0 ≤ b) (c : Config L 3) : 0 ≤ S L b c :=
  Finset.sum_nonneg fun j _ => rate_nonneg hb c j

theorem H_diag (a b : ℝ) (c : Config L 3) :
    switchHam L a b c c = ((switchPotential L a c + S L b c : ℝ) : ℂ) := by
  rw [entry, if_pos rfl]; rfl

theorem H_off (a b : ℝ) {c j : Config L 3} (h : c ≠ j) :
    switchHam L a b c j = -((switchTransitionRate L b c j : ℝ) : ℂ) := by
  rw [entry, if_neg h]

theorem rowsum {a b : ℝ} (hb : 0 ≤ b) (c : Config L 3) :
    ∑ j ∈ Finset.univ.erase c, ‖switchHam L a b c j‖ = S L b c := by
  unfold S
  apply Finset.sum_congr rfl
  intro j hj
  rw [H_off a b (Finset.ne_of_mem_erase hj).symm, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (rate_nonneg hb c j)]

theorem eig_of_mem {A : Matrix (Config L 3) (Config L 3) ℂ} {μ : ℝ} (h : μ ∈ specReal A) :
    Module.End.HasEigenvalue (Matrix.toLin' A) (μ : ℂ) := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
  exact h

theorem mem_of_eig {A : Matrix (Config L 3) (Config L 3) ℂ} {μ : ℝ} (v : Config L 3 → ℂ)
    (hv : v ≠ 0) (h : A.mulVec v = (μ : ℂ) • v) : μ ∈ specReal A := by
  show (μ : ℂ) ∈ spectrum ℂ A
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  refine ⟨?_, hv⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact h

/-- Gershgorin, specialised: every real eigenvalue is at least the potential of some config,
and lies in the disc of that config. -/
theorem gersh {a b : ℝ} (hb : 0 ≤ b) {μ : ℝ} (h : μ ∈ specReal (switchHam L a b)) :
    ∃ k : Config L 3, |μ - (switchPotential L a k + S L b k)| ≤ S L b k := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (eig_of_mem h)
  refine ⟨k, ?_⟩
  rw [Metric.mem_closedBall, rowsum hb, H_diag, dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hk
  exact hk

theorem pot_le {a b : ℝ} (hb : 0 ≤ b) {μ : ℝ} (h : μ ∈ specReal (switchHam L a b)) :
    ∃ k : Config L 3, switchPotential L a k ≤ μ ∧
      |μ - (switchPotential L a k + S L b k)| ≤ S L b k := by
  obtain ⟨k, hk⟩ := gersh hb h
  exact ⟨k, by have := (abs_le.mp hk).1; linarith, hk⟩

def vac (L : ℕ) : Config L 3 := fun _ => 0
def ones (L : ℕ) : Config L 3 := fun _ => 1

theorem rate_vac (b : ℝ) (j : Config L 3) : switchTransitionRate L b (vac L) j = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h; exact h.1 rfl

theorem S_vac (b : ℝ) : S L b (vac L) = 0 := by
  unfold S; simp [rate_vac]

theorem rate_to_vac (b : ℝ) (c : Config L 3) : switchTransitionRate L b c (vac L) = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h
  have := congrFun h.2.2.2 e.2
  simp [vac, Equiv.swap_apply_right] at this
  exact h.1 this.symm

theorem rate_ones (b : ℝ) (j : Config L 3) : switchTransitionRate L b (ones L) j = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h; exact h.2.2.1 rfl

theorem rate_to_ones (b : ℝ) (c : Config L 3) : switchTransitionRate L b c (ones L) = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h
  have h1 := congrFun h.2.2.2 e.1
  have h2 := congrFun h.2.2.2 e.2
  simp [ones, Equiv.swap_apply_right, Equiv.swap_apply_left] at h1 h2
  exact h.2.2.1 (h2.symm.trans h1)

theorem pot_vac (a : ℝ) : switchPotential L a (vac L) = 0 := by
  unfold switchPotential switchOccupiedCount switchBoundaryCount switchBoundaryAt
  simp [vac]

theorem pot_ones (a : ℝ) : switchPotential L a (ones L) = a * (L : ℝ) ^ 2 := by
  unfold switchPotential switchOccupiedCount switchBoundaryCount switchBoundaryAt
  simp [ones, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

theorem mulVec_single (A : Matrix (Config L 3) (Config L 3) ℂ) (c0 : Config L 3) :
    A.mulVec (Pi.single c0 1) = fun c => A c c0 := by
  ext c
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem H_vac_col (a b : ℝ) (c : Config L 3) : switchHam L a b c (vac L) = 0 := by
  by_cases h : c = vac L
  · subst h; rw [H_diag, pot_vac, S_vac]; simp
  · rw [H_off a b h, rate_to_vac]; simp

theorem H_ones_col (a b : ℝ) (c : Config L 3) :
    switchHam L a b c (ones L) = if c = ones L then ((a * (L : ℝ) ^ 2 : ℝ) : ℂ) else 0 := by
  by_cases h : c = ones L
  · subst h; rw [H_diag, pot_ones, if_pos rfl]; unfold S; simp [rate_ones]
  · rw [H_off a b h, rate_to_ones, if_neg h]; simp

theorem zero_mem (a b : ℝ) : (0 : ℝ) ∈ specReal (switchHam L a b) := by
  refine mem_of_eig (Pi.single (vac L) 1) (by simp) ?_
  rw [mulVec_single]; ext c; simp [H_vac_col]

theorem aL_mem (a b : ℝ) : a * (L : ℝ) ^ 2 ∈ specReal (switchHam L a b) := by
  refine mem_of_eig (Pi.single (ones L) 1) (by simp) ?_
  rw [mulVec_single]; ext c
  rw [H_ones_col]
  by_cases h : c = ones L
  · subst h; simp
  · simp [h, Pi.single_apply]

theorem occ_le (c : Config L 3) : (switchOccupiedCount L c : ℝ) ≤ (L : ℝ) ^ 2 := by
  unfold switchOccupiedCount
  have := Finset.card_filter_le (Finset.univ : Finset (Site L)) (fun p => c p ≠ 0)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
  have : ((Finset.univ.filter fun p : Site L => c p ≠ 0).card : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at this; nlinarith

theorem pot_ge_min (a : ℝ) (c : Config L 3) :
    min 0 (a * (L : ℝ) ^ 2) ≤ switchPotential L a c := by
  unfold switchPotential
  have h0 : (0 : ℝ) ≤ (switchOccupiedCount L c : ℝ) := by positivity
  have h1 := occ_le c
  have h2 : (0 : ℝ) ≤ (switchBoundaryCount L c : ℝ) := by positivity
  rcases le_total 0 a with ha | ha
  · have : 0 ≤ a * (switchOccupiedCount L c : ℝ) := mul_nonneg ha h0
    have := min_le_left 0 (a * (L : ℝ) ^ 2); linarith
  · have : a * (L : ℝ) ^ 2 ≤ a * (switchOccupiedCount L c : ℝ) :=
      mul_le_mul_of_nonpos_left h1 ha
    have := min_le_right 0 (a * (L : ℝ) ^ 2); linarith

theorem no_bdry_const (k : Config L 3) (hL : 0 < L)
    (hrow : ∀ e ∈ rowEdges L, ¬ switchBoundaryAt k e)
    (hcol : ∀ e ∈ colEdges L, ¬ switchBoundaryAt k e) :
    ∀ s : Site L, (k s = 0 ↔ k (⟨0, hL⟩, ⟨0, hL⟩) = 0) := by
  have edge : ∀ e : Site L × Site L, ¬ switchBoundaryAt k e → (k e.1 = 0 ↔ k e.2 = 0) := by
    intro e he; unfold switchBoundaryAt at he; tauto
  have hr : ∀ (i : Fin L) (j : ℕ) (hj : j < L), (k (i, ⟨j, hj⟩) = 0 ↔ k (i, ⟨0, hL⟩) = 0) := by
    intro i j
    induction j with
    | zero => intro _; exact Iff.rfl
    | succ j ih =>
      intro hj
      have hm : ((i, ⟨j, by omega⟩), (i, ⟨j + 1, hj⟩)) ∈ rowEdges L := by
        simp [rowEdges]
      exact (edge _ (hrow _ hm)).symm.trans (ih (by omega))
  have hc : ∀ (i : ℕ) (hi : i < L), (k (⟨i, hi⟩, ⟨0, hL⟩) = 0 ↔ k (⟨0, hL⟩, ⟨0, hL⟩) = 0) := by
    intro i
    induction i with
    | zero => intro _; exact Iff.rfl
    | succ i ih =>
      intro hi
      have hm : ((⟨i, by omega⟩, ⟨0, hL⟩), (⟨i + 1, hi⟩, ⟨0, hL⟩)) ∈ colEdges L := by
        simp [colEdges]
      exact (edge _ (hcol _ hm)).symm.trans (ih (by omega))
  rintro ⟨i, j⟩
  exact (hr i j.1 j.2).trans (hc i.1 i.2)

theorem pot_ge_one {a : ℝ} (ha : 0 < a) (hL : 0 < L) (haL : 1 ≤ a * (L : ℝ) ^ 2)
    (k : Config L 3) (hk : k ≠ vac L) : 1 ≤ switchPotential L a k := by
  unfold switchPotential
  have h0 : (0 : ℝ) ≤ (switchOccupiedCount L k : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (switchBoundaryCount L k : ℝ) := by positivity
  by_cases hall : ∀ s, k s ≠ 0
  · have : switchOccupiedCount L k = L * L := by
      unfold switchOccupiedCount
      rw [Finset.filter_true_of_mem (fun s _ => hall s)]
      simp [Finset.card_univ]
    rw [this]; push_cast
    nlinarith
  · push_neg at hall
    obtain ⟨q, hq⟩ := hall
    obtain ⟨p, hp⟩ : ∃ p, k p ≠ 0 := by
      by_contra h; push_neg at h; exact hk (funext h)
    have hb : 1 ≤ switchBoundaryCount L k := by
      by_contra hcon
      have hz : switchBoundaryCount L k = 0 := by omega
      unfold switchBoundaryCount at hz
      have h1 : ((rowEdges L).filter (switchBoundaryAt k)).card = 0 := by omega
      have h2' : ((colEdges L).filter (switchBoundaryAt k)).card = 0 := by omega
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1 h2'
      have hc := no_bdry_const k hL h1 h2'
      exact hp ((hc p).mpr ((hc q).mp hq))
    have : (1 : ℝ) ≤ (switchBoundaryCount L k : ℝ) := by exact_mod_cast hb
    have : 0 ≤ a * (switchOccupiedCount L k : ℝ) := mul_nonneg ha.le h0
    linarith

theorem Hvac_mulVec (a b : ℝ) :
    (switchHam L a b).mulVec (Pi.single (vac L) 1) = 0 := by
  rw [mulVec_single]; ext c; simp [H_vac_col]

theorem eigenspace_zero {a b : ℝ} (hb : 0 ≤ b) (ha : 0 < a) (hL : 0 < L)
    (haL : 1 ≤ a * (L : ℝ) ^ 2) :
    Module.End.eigenspace (Matrix.toLin' (switchHam L a b)) 0 =
      Submodule.span ℂ {(Pi.single (vac L) 1 : Config L 3 → ℂ)} := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, zero_smul] at hv
    set w := v - v (vac L) • (Pi.single (vac L) 1 : Config L 3 → ℂ) with hw
    have hHw : (switchHam L a b).mulVec w = 0 := by
      rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, Hvac_mulVec, hv]; simp
    have hwv : w (vac L) = 0 := by simp [hw]
    let H' : Matrix (Config L 3) (Config L 3) ℂ :=
      switchHam L a b + Matrix.of (fun k j => if k = vac L ∧ j = vac L then 1 else 0)
    have hH'w : H'.mulVec w = 0 := by
      simp only [H', Matrix.add_mulVec, hHw, zero_add]
      ext k
      by_cases hk : k = vac L
      · subst hk; simp [Matrix.mulVec, dotProduct, hwv]
      · simp [Matrix.mulVec, dotProduct, hk]
    have hdet : H'.det ≠ 0 := by
      apply det_ne_zero_of_sum_row_lt_diag
      intro k
      have hsum : ∑ j ∈ Finset.univ.erase k, ‖H' k j‖ = S L b k := by
        rw [← rowsum (a := a) hb k]
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.ne_of_mem_erase hj
        simp only [H', Matrix.add_apply, Matrix.of_apply]
        rw [if_neg (fun h => hjk (h.2.trans h.1.symm)), add_zero]
      rw [hsum]
      simp only [H', Matrix.add_apply, Matrix.of_apply]
      by_cases hk : k = vac L
      · subst hk
        rw [S_vac, if_pos ⟨rfl, rfl⟩, H_diag, pot_vac, S_vac]; simp
      · rw [if_neg (fun h => hk h.1), add_zero, H_diag, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (by linarith [pot_ge_one ha hL haL k hk]) (S_nonneg hb k))]
        linarith [pot_ge_one ha hL haL k hk]
    have hw0 : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hH'w
    rw [Submodule.mem_span_singleton]
    refine ⟨v (vac L), ?_⟩
    rw [hw, sub_eq_zero] at hw0
    exact hw0.symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show _ ∈ Module.End.eigenspace _ _
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Hvac_mulVec, zero_smul]

end AgentBUSG

open AgentBUSG in
theorem _root_.solution
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    ∀ L : ℕ, 2 ≤ L →
      1 ≤ a * (L : ℝ) ^ 2 →
        eigMultiplicity (switchHam L a b) 0 = 1 ∧
        ∀ μ ∈ specReal (switchHam L a b), μ ≠ 0 → 1 ≤ μ := by
  intro L hL haL
  have hL0 : 0 < L := by omega
  have hapos : 0 < a := by
    by_contra h; push_neg at h
    have : a * (L : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  refine ⟨?_, fun μ hμ hne => ?_⟩
  · unfold eigMultiplicity
    rw [Complex.ofReal_zero, eigenspace_zero hb.le hapos hL0 haL, finrank_span_singleton]
    simp
  · obtain ⟨k, hk, hk2⟩ := pot_le hb.le hμ
    by_cases hkv : k = vac L
    · subst hkv
      rw [pot_vac, S_vac] at hk2
      exact absurd (abs_nonpos_iff.mp (by simpa using hk2)) hne
    · exact (pot_ge_one hapos hL0 haL k hkv).trans hk
#print axioms solution
