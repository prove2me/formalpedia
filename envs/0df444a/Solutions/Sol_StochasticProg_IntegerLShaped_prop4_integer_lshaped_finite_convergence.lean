-- Prove2me | solution 1 for StochasticProg.IntegerLShaped.prop4_integer_lshaped_finite_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:04:25.935026+00:00
-- url     : https://prove2.me/submissions/41fbbbaa-ea6b-4d3a-a66c-c9cf28ebedac

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Algorithm

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

/-- Generic finite-termination lemma: a relation strictly increasing the cardinality of
finsets of a finite type admits a maximal run of bounded length. -/
theorem aux_ils_path {α : Type} [Fintype α] [DecidableEq α]
    (R : Finset α → Finset α → Prop) (hR : ∀ C C', R C C' → C.card < C'.card) :
    ∀ (k : ℕ) (C : Finset α), Fintype.card α - C.card = k →
      ∃ (N : ℕ) (path : ℕ → Finset α), N + C.card ≤ Fintype.card α ∧ path 0 = C ∧
        (∀ i, i < N → R (path i) (path (i + 1))) ∧ (∀ C', ¬ R (path N) C') := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro C hk
  by_cases h : ∃ C', R C C'
  · obtain ⟨C', hC'⟩ := h
    have hlt := hR C C' hC'
    have hle : C'.card ≤ Fintype.card α := Finset.card_le_univ C'
    obtain ⟨N, path, hN, h0, hsteps, hterm⟩ :=
      ih (Fintype.card α - C'.card) (by omega) C' rfl
    refine ⟨N + 1, fun i => match i with | 0 => C | j + 1 => path j, by omega, rfl, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => simpa [h0] using hC'
      | succ j => exact hsteps j (by omega)
    · simpa using hterm
  · simp only [not_exists] at h
    exact ⟨0, fun _ => C, by have := Finset.card_le_univ C; omega, rfl,
      fun i hi => absurd hi (by omega), h⟩

variable {n1 n2 m1 m2 K : ℕ}

theorem aux_ils_binary_eq {x : Fin n1 → ℝ} (hx : Binary x) :
    x = indicator (Finset.univ.filter (fun i => x i = 1)) := by
  funext i
  rcases hx i with h | h <;> simp [indicator, h]

theorem aux_ils_indicator_binary (S : Finset (Fin n1)) : Binary (indicator S) := by
  intro i
  by_cases h : i ∈ S <;> simp [indicator, h]

theorem aux_ils_delta (S S' : Finset (Fin n1)) :
    delta S (indicator S') = ((S ∩ S').card : ℝ) - ((Sᶜ ∩ S').card : ℝ) := by
  simp [delta, indicator, Finset.sum_ite_mem]

theorem aux_ils_delta_self (S : Finset (Fin n1)) :
    delta S (indicator S) = (S.card : ℝ) := by
  have h0 : Sᶜ ∩ S = ∅ := by ext i; simp
  rw [aux_ils_delta, Finset.inter_self, h0]
  simp

theorem aux_ils_delta_ne {S S' : Finset (Fin n1)} (hne : S' ≠ S) :
    delta S (indicator S') ≤ (S.card : ℝ) - 1 := by
  rw [aux_ils_delta]
  have key : (S ∩ S').card + 1 ≤ S.card + (Sᶜ ∩ S').card := by
    by_cases hsub : S ⊆ S'
    · have h1 : S ∩ S' = S := Finset.inter_eq_left.mpr hsub
      have h2 : ¬ S' ⊆ S := fun h => hne (Finset.Subset.antisymm h hsub)
      obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp h2
      have h3 : 0 < (Sᶜ ∩ S').card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hni, hi⟩⟩
      rw [h1]; omega
    · obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hsub
      have h3 : (S ∩ S').card < S.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.inter_subset_left, fun h => hni ?_⟩
        exact (Finset.mem_inter.mp (h hi)).2
      omega
  have key' : ((S ∩ S').card : ℝ) + 1 ≤ (S.card : ℝ) + ((Sᶜ ∩ S').card : ℝ) := by
    exact_mod_cast key
  linarith

theorem aux_ils_cut_self (L q : ℝ) (S : Finset (Fin n1)) :
    cutRHS L q S (indicator S) = q := by
  simp only [cutRHS, aux_ils_delta_self]
  ring

theorem aux_ils_cut_ne {L q : ℝ} (hq : L ≤ q) {S S' : Finset (Fin n1)} (hne : S' ≠ S) :
    cutRHS L q S (indicator S') ≤ L := by
  unfold cutRHS
  have h := aux_ils_delta_ne hne
  have : (q - L) * delta S (indicator S') ≤ (q - L) * ((S.card : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  linarith

/-- The choice of `qS`: the true recourse value `Q(x)` at the indicator point, clipped
below by `L` (which does not change it on binary feasible points). -/
noncomputable def aux_ils_qS (d : Data n1 n2 m1 m2 K) (L : ℝ) (S : Finset (Fin n1)) : ℝ :=
  max L (QY d (indicator S)).toReal

theorem aux_ils_qS_ge (d : Data n1 n2 m1 m2 K) (L : ℝ) (S : Finset (Fin n1)) :
    L ≤ aux_ils_qS d L S := le_max_left _ _

theorem aux_ils_qS_eq (d : Data n1 n2 m1 m2 K) (L : ℝ)
    (hL : ∀ x, x ∈ K1X d → Binary x → (L : EReal) ≤ QY d x)
    (hrcr : RelativelyCompleteRecourse d) {S : Finset (Fin n1)}
    (hS : indicator S ∈ K1X d) :
    ((aux_ils_qS d L S : ℝ) : EReal) = QY d (indicator S) := by
  have hLe := hL _ hS (aux_ils_indicator_binary S)
  have htop : QY d (indicator S) ≠ ⊤ := hrcr hS
  have hbot : QY d (indicator S) ≠ ⊥ := by
    intro h; rw [h] at hLe; exact (EReal.coe_ne_bot L) (le_bot_iff.mp hLe)
  have h1 : L ≤ (QY d (indicator S)).toReal := by
    have := EReal.toReal_le_toReal hLe (EReal.coe_ne_bot L) htop
    simpa using this
  unfold aux_ils_qS
  rw [max_eq_right h1, EReal.coe_toReal htop hbot]

theorem aux_ils_final (d : Data n1 n2 m1 m2 K) (L : ℝ)
    (hL : ∀ x, x ∈ K1X d → Binary x → (L : EReal) ≤ QY d x)
    (hrcr : RelativelyCompleteRecourse d) (T : State n1)
    (hterm : ∀ Cuts', ¬ Step d L (aux_ils_qS d L) T Cuts') :
    (∀ x, x ∈ K1X d → ¬ Binary x) ∨
      (∃ x θ, IsBBOptimal d T L (aux_ils_qS d L) x θ ∧
        ∀ x', x' ∈ K1X d → Binary x' → objY d x ≤ objY d x') := by
  classical
  set qS := aux_ils_qS d L with hqSdef
  by_cases hex : ∃ x, x ∈ K1X d ∧ Binary x
  swap
  · left
    intro x hx hb
    exact hex ⟨x, hx, hb⟩
  right
  obtain ⟨x1, hx1, hb1⟩ := hex
  set B : Finset (Finset (Fin n1)) :=
    Finset.univ.filter (fun S => indicator S ∈ K1X d) with hBdef
  have hB : ∀ x', x' ∈ K1X d → Binary x' →
      (Finset.univ.filter (fun i => x' i = 1)) ∈ B ∧
        x' = indicator (Finset.univ.filter (fun i => x' i = 1)) := by
    intro x' hx' hb'
    have heq := aux_ils_binary_eq hb'
    refine ⟨?_, heq⟩
    rw [hBdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, heq ▸ hx'⟩
  have hBne : B.Nonempty := ⟨_, (hB x1 hx1 hb1).1⟩
  have hmemB : ∀ S, S ∈ B → indicator S ∈ K1X d := by
    intro S hS
    rw [hBdef, Finset.mem_filter] at hS
    exact hS.2
  rcases Finset.eq_empty_or_nonempty T with hT | hT
  · -- empty cut set: a step is always available, contradiction
    exfalso
    obtain ⟨S0, hS0, hmin⟩ := Finset.exists_min_image B (fun S => dotProduct d.c (indicator S)) hBne
    have hopt : IsBBOptimal d T L qS (indicator S0) (qS S0 - 1) := by
      refine ⟨hmemB S0 hS0, aux_ils_indicator_binary S0, ?_, ?_⟩
      · intro hne; rw [hT] at hne; exact absurd hne (Finset.not_nonempty_empty)
      · have hnn : ¬ T.Nonempty := by rw [hT]; exact Finset.not_nonempty_empty
        rw [if_neg hnn]
        intro x' hx' hb'
        obtain ⟨hmem, heq⟩ := hB x' hx' hb'
        rw [heq]
        exact hmin _ hmem
    have hnew : S0 ∉ T := by rw [hT]; exact Finset.notMem_empty S0
    exact hterm _ (Step.cut T (indicator S0) (qS S0 - 1) hopt S0 rfl hnew
      (aux_ils_qS_eq d L hL hrcr (hmemB S0 hS0)) (by linarith))
  · -- nonempty cut set
    let th : (Fin n1 → ℝ) → ℝ := fun x => T.sup' hT (fun S => cutRHS L (qS S) S x)
    obtain ⟨S0, hS0, hmin⟩ := Finset.exists_min_image B
      (fun S => dotProduct d.c (indicator S) + th (indicator S)) hBne
    have hcf : ∀ x, CutsFeasible d T L qS x (th x) := by
      intro x S hS
      exact Finset.le_sup' (fun S => cutRHS L (qS S) S x) hS
    have hopt : IsBBOptimal d T L qS (indicator S0) (th (indicator S0)) := by
      refine ⟨hmemB S0 hS0, aux_ils_indicator_binary S0, fun _ => hcf _, ?_⟩
      rw [if_pos hT]
      intro x' θ' hx' hb' hcf'
      obtain ⟨hmem, heq⟩ := hB x' hx' hb'
      have h1 := hmin _ hmem
      have h2 : th x' ≤ θ' := Finset.sup'_le hT _ (fun S hS => hcf' S hS)
      rw [← heq] at h1
      linarith
    -- no step ⇒ θ₀ ≥ qS S0
    have hge : qS S0 ≤ th (indicator S0) := by
      by_cases hin : S0 ∈ T
      · have := hcf (indicator S0) S0 hin
        rw [aux_ils_cut_self] at this
        exact this
      · by_contra hlt
        rw [not_le] at hlt
        exact hterm _ (Step.cut T (indicator S0) (th (indicator S0)) hopt S0 rfl hin
          (aux_ils_qS_eq d L hL hrcr (hmemB S0 hS0)) hlt)
    -- validity of the cuts on binary feasible points
    have hvalid : ∀ S', S' ∈ B → th (indicator S') ≤ qS S' := by
      intro S' _
      apply Finset.sup'_le
      intro S _
      by_cases hSS : S' = S
      · subst hSS
        rw [aux_ils_cut_self]
      · exact le_trans (aux_ils_cut_ne (aux_ils_qS_ge d L S) hSS) (aux_ils_qS_ge d L S')
    refine ⟨indicator S0, th (indicator S0), hopt, ?_⟩
    intro x' hx' hb'
    obtain ⟨hmem, heq⟩ := hB x' hx' hb'
    set S' := Finset.univ.filter (fun i => x' i = 1)
    have h1 := hmin S' hmem
    have h2 := hvalid S' hmem
    unfold objY
    rw [← aux_ils_qS_eq d L hL hrcr (hmemB S0 hS0), heq,
      ← aux_ils_qS_eq d L hL hrcr (hmemB S' hmem), ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    linarith

end StochasticProg.IntegerLShaped

open StochasticProg.IntegerLShaped
open StochasticProg.Recourse

theorem solution {n1 n2 m1 m2 K : ℕ} (d : StochasticProg.IntegerLShaped.Data n1 n2 m1 m2 K) (L : ℝ)
    (hL : ∀ x, x ∈ K1X d → Binary x → (L : EReal) ≤ QY d x)
    (hrcr : RelativelyCompleteRecourse d) :
    ∃ (N : ℕ) (qS : Finset (Fin n1) → ℝ) (path : ℕ → State n1),
      N ≤ Fintype.card (Finset (Fin n1)) ∧
      path 0 = ∅ ∧
      (∀ i, i < N → Step d L qS (path i) (path (i + 1))) ∧
      (∀ Cuts', ¬ Step d L qS (path N) Cuts') ∧
      ((∀ x, x ∈ K1X d → ¬ Binary x) ∨
        (∃ x θ, IsBBOptimal d (path N) L qS x θ ∧
          ∀ x', x' ∈ K1X d → Binary x' → objY d x ≤ objY d x')) := by
  have hR : ∀ C C', Step d L (aux_ils_qS d L) C C' → C.card < C'.card := by
    intro C C' h
    cases h with
    | cut x θ hopt S hS hnew hqS hviol =>
      rw [Finset.card_insert_of_notMem hnew]
      omega
  obtain ⟨N, path, hN, h0, hsteps, hterm⟩ :=
    aux_ils_path (Step d L (aux_ils_qS d L)) hR _ ∅ rfl
  refine ⟨N, aux_ils_qS d L, path, by simpa using hN, h0, hsteps, hterm, ?_⟩
  exact aux_ils_final d L hL hrcr (path N) hterm
