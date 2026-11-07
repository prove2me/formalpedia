-- Prove2me | solution 1 for PermBlockchain.Transfers.proposition_4_9_resolving_adoption_failures
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T19:42:23.350273+00:00
-- url     : https://prove2.me/submissions/bd668f1b-7677-4f43-ad8d-c05558289148

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_IsTransferEquilibrium
import Definitions.Def_PermBlockchain_Transfers_SelfFinancing
import Definitions.Def_PermBlockchain_Transfers_FullAdoption
import Definitions.Def_PermBlockchain_Transfers_Assumption1

set_option autoImplicit false
set_option linter.all false

namespace E78PB
open PermBlockchain.Transfers MeasureTheory

/-! ### Finite types and assignments -/

theorem sum_horiz (f : Horiz → ℝ) : ∑ t, f t = f .A + f .B := by
  rw [show (Finset.univ : Finset Horiz) = {.A, .B} from rfl, Finset.sum_pair (by decide)]

theorem sum_vert (f : Vert → ℝ) : ∑ v, f v = f .hi + f .lo := by
  rw [show (Finset.univ : Finset Vert) = {.hi, .lo} from rfl, Finset.sum_pair (by decide)]

theorem card_mtype : Fintype.card MType = 4 := by
  rw [Fintype.card_prod]
  show Finset.card ({.A, .B} : Finset Horiz) * Finset.card ({.hi, .lo} : Finset Vert) = 4
  rw [Finset.card_pair (by decide), Finset.card_pair (by decide)]

theorem mem_assign {m : ℕ} {θ : Mfr m → MType} :
    θ ∈ Assignments m ↔ ∀ τ : MType, (Finset.univ.filter (fun i => θ i = τ)).card = m := by
  unfold Assignments
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem comp_perm_mem {m : ℕ} {θ : Mfr m → MType} (hθ : θ ∈ Assignments m)
    (σ : Equiv.Perm (Mfr m)) : θ ∘ σ ∈ Assignments m := by
  rw [mem_assign] at hθ ⊢
  intro τ
  exact (Finset.card_equiv σ (fun i => by simp)).trans (hθ τ)

noncomputable def eqv (m : ℕ) : MType × Fin m ≃ Mfr m :=
  Fintype.equivOfCardEq (by rw [Fintype.card_prod, card_mtype, Fintype.card_fin, Fintype.card_fin])

noncomputable def base (m : ℕ) : Mfr m → MType := fun i => ((eqv m).symm i).1

theorem base_eqv (m : ℕ) (τ : MType) (k : Fin m) : base m (eqv m (τ, k)) = τ := by
  simp [base]

theorem base_mem (m : ℕ) : base m ∈ Assignments m := by
  rw [mem_assign]
  intro τ
  have h1 : (Finset.univ.filter (fun i => base m i = τ)).card =
      (Finset.univ.filter (fun p : MType × Fin m => p.1 = τ)).card :=
    Finset.card_equiv (eqv m).symm (fun i => Iff.intro
      (fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [base] using (Finset.mem_filter.1 h).2⟩)
      (fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [base] using (Finset.mem_filter.1 h).2⟩))
  have h2 : (Finset.univ.filter (fun p : MType × Fin m => p.1 = τ)) =
      ({τ} : Finset MType) ×ˢ (Finset.univ : Finset (Fin m)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [h1, h2, Finset.card_product]
  simp

theorem card_lo {m : ℕ} {θ : Mfr m → MType} (hθ : θ ∈ Assignments m) :
    (Finset.univ.filter (fun i => (θ i).2 = Vert.lo)).card = 2 * m := by
  have e : Finset.univ.filter (fun i => (θ i).2 = Vert.lo) =
      Finset.univ.filter (fun i => θ i = (.A, .lo)) ∪ Finset.univ.filter (fun i => θ i = (.B, .lo)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rcases θ i with ⟨q, v⟩
    cases q <;> cases v <;> simp
  rw [e, Finset.card_union_of_disjoint, (mem_assign.1 hθ) _, (mem_assign.1 hθ) _]
  · ring
  · rw [Finset.disjoint_filter]
    intro i _ h1 h2
    rw [h1] at h2
    simp at h2

/-! ### Punishing belief -/

section pun
variable {m : ℕ} (hm : 0 < m)

noncomputable def pt (τ : MType) : Mfr m := eqv m (τ, ⟨0, hm⟩)

noncomputable def th1 (j : Mfr m) : Mfr m → MType :=
  base m ∘ Equiv.swap j (pt hm (.A, .lo))

noncomputable def j2 (j : Mfr m) : Mfr m := Equiv.swap j (pt hm (.A, .lo)) (pt hm (.B, .lo))

noncomputable def th2 (j : Mfr m) : Mfr m → MType := th1 hm j ∘ Equiv.swap j (j2 hm j)

theorem th1_mem (j : Mfr m) : th1 hm j ∈ Assignments m := comp_perm_mem (base_mem m) _

theorem th2_mem (j : Mfr m) : th2 hm j ∈ Assignments m := comp_perm_mem (th1_mem hm j) _

theorem th1_swapped (j y : Mfr m) :
    th1 hm j (Equiv.swap j (pt hm (.A, .lo)) y) = base m y := by
  simp [th1, Equiv.swap_apply_self]

theorem th1_j (j : Mfr m) : th1 hm j j = (.A, .lo) := by
  simp [th1, pt, base_eqv]

theorem th1_j2 (j : Mfr m) : th1 hm j (j2 hm j) = (.B, .lo) := by
  rw [j2, th1_swapped]; simp [pt, base_eqv]

theorem th2_j (j : Mfr m) : th2 hm j j = (.B, .lo) := by
  simp only [th2, Function.comp_apply, Equiv.swap_apply_left]
  exact th1_j2 hm j

theorem rival (j : Mfr m) (t : Horiz) :
    ∃ k, k ≠ j ∧ th1 hm j k = (t, .hi) ∧ th2 hm j k = (t, .hi) := by
  refine ⟨Equiv.swap j (pt hm (.A, .lo)) (pt hm (t, .hi)), ?_, ?_, ?_⟩
  · intro h
    have := th1_swapped hm j (pt hm (t, .hi))
    rw [h, th1_j] at this
    simp [pt, base_eqv] at this
  · rw [th1_swapped]; simp [pt, base_eqv]
  · set k := Equiv.swap j (pt hm (.A, .lo)) (pt hm (t, .hi))
    have hk1 : th1 hm j k = (t, .hi) := by rw [th1_swapped]; simp [pt, base_eqv]
    have h1 : k ≠ j := by
      intro h; rw [h, th1_j] at hk1; simp at hk1
    have h2 : k ≠ j2 hm j := by
      intro h; rw [h, th1_j2] at hk1; simp at hk1
    simp only [th2, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hk1]

noncomputable def pun (j : Mfr m) (θ' : Mfr m → MType) : ℝ :=
  (if θ' = th1 hm j then 1 / 2 else 0) + (if θ' = th2 hm j then 1 / 2 else 0)

theorem sum_pun (j : Mfr m) (f : (Mfr m → MType) → ℝ) :
    ∑ θ' ∈ Assignments m, pun hm j θ' * f θ' = f (th1 hm j) / 2 + f (th2 hm j) / 2 := by
  simp only [pun, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (th1_mem hm j), if_pos (th2_mem hm j)]
  ring

end pun

/-! ### Uniform prior and its symmetric average -/

noncomputable def unif (m : ℕ) (θ' : Mfr m → MType) : ℝ :=
  if θ' ∈ Assignments m then 1 / ((Assignments m).card : ℝ) else 0

theorem sum_assign_swap {m : ℕ} (g : MType → ℝ) (i j : Mfr m) :
    ∑ θ' ∈ Assignments m, g (θ' i) = ∑ θ' ∈ Assignments m, g (θ' j) := by
  refine Finset.sum_nbij' (fun θ' => θ' ∘ Equiv.swap i j) (fun θ' => θ' ∘ Equiv.swap i j)
    (fun θ' h => comp_perm_mem h _) (fun θ' h => comp_perm_mem h _) ?_ ?_ ?_
  · intro θ' _; funext k; simp [Equiv.swap_apply_self]
  · intro θ' _; funext k; simp [Equiv.swap_apply_self]
  · intro θ' _; simp

theorem sum_over_mfr {m : ℕ} {θ' : Mfr m → MType} (h : θ' ∈ Assignments m) (g : MType → ℝ) :
    ∑ i, g (θ' i) = m * ∑ τ, g τ := by
  rw [← Finset.sum_fiberwise Finset.univ θ' (fun i => g (θ' i)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => g τ) (fun i hi => by rw [(Finset.mem_filter.1 hi).2])]
  rw [Finset.sum_const, (mem_assign.1 h) τ, nsmul_eq_mul]

theorem sum_gv (H L h l : ℝ) (t : Horiz) :
    ∑ τ : MType, goodValue H L h l τ t = 2 * (H + L + h + l) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_horiz, sum_vert]
  cases t <;> simp [goodValue] <;> ring

theorem expValue_unif {m : ℕ} (hm : 0 < m) (H L h l : ℝ) (i : Mfr m) (t : Horiz) :
    expValue H L h l (unif m) i t = (H + L + h + l) / 2 := by
  have hN : (0 : ℝ) < (Assignments m).card := by
    exact_mod_cast Finset.card_pos.2 ⟨_, base_mem m⟩
  have hE : ∀ j, expValue H L h l (unif m) j t =
      (1 / ((Assignments m).card : ℝ)) * ∑ θ' ∈ Assignments m, goodValue H L h l (θ' j) t := by
    intro j
    unfold expValue unif
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun θ' h' => by rw [if_pos h'])
  have hsym : ∀ j, expValue H L h l (unif m) j t = expValue H L h l (unif m) i t := by
    intro j
    rw [hE, hE, sum_assign_swap (fun τ => goodValue H L h l τ t) j i]
  have htot : ∑ j : Mfr m, expValue H L h l (unif m) j t = m * (2 * (H + L + h + l)) := by
    simp_rw [hE]
    rw [← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun θ' h' => sum_over_mfr h' (fun τ => goodValue H L h l τ t))]
    rw [Finset.sum_const, nsmul_eq_mul, sum_gv]
    field_simp
  rw [Finset.sum_congr rfl (fun j _ => hsym j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at htot
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast at htot
  apply mul_left_cancel₀ (show (4 * (m : ℝ)) ≠ 0 by positivity)
  linear_combination htot

/-! ### Beliefs -/

def x0 (m : ℕ) (P : ℝ) : Hist m := (fun _ => true, fun _ => P)

open Classical in
noncomputable def dev {m : ℕ} (hm : 0 < m) (P : ℝ) (x : Hist m) : Mfr m :=
  if hx : ∃ j, ¬ (x.1 j = true ∧ x.2 j = P) then Classical.choose hx else pt hm (.A, .lo)

open Classical in
noncomputable def prior0 {m : ℕ} (hm : 0 < m) (P : ℝ) (x : Hist m) (θ' : Mfr m → MType) : ℝ :=
  if x = x0 m P then unif m θ' else pun hm (dev hm P x) θ'

noncomputable def bel {m : ℕ} (hm : 0 < m) (P : ℝ) : BeliefSystem m := fun x b r θ' =>
  if b = true then
    (if 0 < ∑ θ'' ∈ agreeSet r, prior0 hm P x θ'' then
      (if θ' ∈ agreeSet r then prior0 hm P x θ' / ∑ θ'' ∈ agreeSet r, prior0 hm P x θ'' else 0)
     else (if θ' ∈ agreeSet r then 1 / ((agreeSet r).card : ℝ) else 0))
  else prior0 hm P x θ'

theorem agree_noInfo (m : ℕ) : agreeSet (noInfo : Mfr m → Option MType) = Assignments m := by
  unfold agreeSet
  apply Finset.filter_true_of_mem
  intro θ _ j τ h
  simp [noInfo] at h

theorem revealed_false {m : ℕ} (θ : Mfr m → MType) (x : Hist m) : revealed false θ x = noInfo := by
  funext j; simp [revealed, noInfo]

theorem mem_agree_self {m : ℕ} {θ : Mfr m → MType} (hθ : θ ∈ Assignments m) (b : Bool)
    (x : Hist m) : θ ∈ agreeSet (revealed b θ x) := by
  unfold agreeSet
  rw [Finset.mem_filter]
  refine ⟨hθ, fun j τ h => ?_⟩
  simp only [revealed] at h
  split_ifs at h <;> simp_all

theorem prior0_prob {m : ℕ} (hm : 0 < m) (P : ℝ) (x : Hist m) :
    (∀ θ', 0 ≤ prior0 hm P x θ') ∧ ∑ θ' ∈ Assignments m, prior0 hm P x θ' = 1 ∧
      (∀ θ', 0 < prior0 hm P x θ' → θ' ∈ Assignments m) := by
  have hN : (0 : ℝ) < (Assignments m).card := by
    exact_mod_cast Finset.card_pos.2 ⟨_, base_mem m⟩
  unfold prior0
  split_ifs with hx
  · refine ⟨fun θ' => ?_, ?_, fun θ' h => ?_⟩
    · unfold unif; split_ifs <;> positivity
    · rw [Finset.sum_congr rfl (fun θ' h' => by unfold unif; rw [if_pos h']), Finset.sum_const,
        nsmul_eq_mul]
      field_simp
    · unfold unif at h; split_ifs at h with h'
      · exact h'
      · exact absurd h (lt_irrefl 0)
  · refine ⟨fun θ' => ?_, ?_, fun θ' h => ?_⟩
    · unfold pun; split_ifs <;> norm_num
    · have := sum_pun hm (dev hm P x) (fun _ => 1)
      simp only [mul_one] at this
      rw [this]; norm_num
    · unfold pun at h
      by_cases h1 : θ' = th1 hm (dev hm P x)
      · rw [h1]; exact th1_mem hm _
      · by_cases h2 : θ' = th2 hm (dev hm P x)
        · rw [h2]; exact th2_mem hm _
        · rw [if_neg h1, if_neg h2] at h; norm_num at h

theorem bel_prob {m : ℕ} (hm : 0 < m) (P : ℝ) (x : Hist m) (b : Bool) {θ : Mfr m → MType}
    (hθ : θ ∈ Assignments m) :
    (∀ θ', 0 ≤ bel hm P x b (revealed b θ x) θ') ∧
    (∀ θ', 0 < bel hm P x b (revealed b θ x) θ' → θ' ∈ agreeSet (revealed b θ x)) ∧
    ∑ θ' ∈ Assignments m, bel hm P x b (revealed b θ x) θ' = 1 := by
  obtain ⟨p0, p1, p2⟩ := prior0_prob hm P x
  cases b with
  | false =>
    simp only [bel, Bool.false_eq_true, ↓reduceIte, revealed_false, agree_noInfo]
    exact ⟨p0, p2, p1⟩
  | true =>
    set r := revealed true θ x with hr
    have hsub : agreeSet r ⊆ Assignments m := Finset.filter_subset _ _
    have hsum : ∀ f : (Mfr m → MType) → ℝ,
        ∑ θ' ∈ Assignments m, (if θ' ∈ agreeSet r then f θ' else 0) = ∑ θ' ∈ agreeSet r, f θ' := by
      intro f
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    simp only [bel, ↓reduceIte]
    split_ifs with hpos
    · refine ⟨fun θ' => ?_, fun θ' h => ?_, ?_⟩
      · split_ifs
        · exact div_nonneg (p0 _) hpos.le
        · exact le_rfl
      · split_ifs at h with hm'
        · exact hm'
        · exact absurd h (lt_irrefl 0)
      · rw [hsum, ← Finset.sum_div, div_self hpos.ne']
    · have hne : (0 : ℝ) < (agreeSet r).card := by
        exact_mod_cast Finset.card_pos.2 ⟨θ, mem_agree_self hθ true x⟩
      refine ⟨fun θ' => ?_, fun θ' h => ?_, ?_⟩
      · split_ifs
        · positivity
        · exact le_rfl
      · split_ifs at h with hm'
        · exact hm'
        · exact absurd h (lt_irrefl 0)
      · rw [hsum, Finset.sum_const, nsmul_eq_mul]
        field_simp

def actP {m : ℕ} (P ψ γ : ℝ) : Strategy m := fun _ τ => (true, P, if τ.2 = .hi then γ else ψ)

theorem hist_onPath {m : ℕ} (P ψ γ : ℝ) (θ : Mfr m → MType) :
    histOf (onPath (actP P ψ γ) θ) = x0 m P := rfl

theorem bel_consistent {m : ℕ} (hm : 0 < m) (P ψ γ : ℝ) :
    IsConsistentBelief (actP (m := m) P ψ γ) (bel hm P) := by
  refine ⟨fun x b θ hθ => bel_prob hm P x b hθ, fun x hne θ' => ?_, fun x θ _ hpos θ' => ?_⟩
  · have hx : x = x0 m P := by
      obtain ⟨θ'', h''⟩ := hne
      unfold consistentSet at h''
      rw [Finset.mem_filter] at h''
      rw [← h''.2]; rfl
    have hcs : consistentSet (actP P ψ γ) x = Assignments m := by
      unfold consistentSet
      apply Finset.filter_true_of_mem
      intro θ'' _
      rw [hx]; rfl
    subst hx
    rw [hcs]
    show prior0 hm P (x0 m P) θ' = _
    rw [prior0, if_pos rfl]
    rfl
  · have hpos' : 0 < ∑ θ'' ∈ agreeSet (revealed true θ x), prior0 hm P x θ'' := hpos
    simp only [bel, Bool.false_eq_true, ↓reduceIte, if_pos hpos']

/-! ### Purchase rule -/

noncomputable def uvec {m : ℕ} (H L h l : ℝ) (β : BeliefSystem m) (t : Horiz) (x : Hist m)
    (b : Bool) (r : Mfr m → Option MType) (i : Mfr m) : ℝ :=
  utility H L h l (β x b r) x i t

noncomputable def ustar {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ u

theorem le_ustar {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (i : Mfr m) : u i ≤ ustar hm u :=
  Finset.le_sup' u (Finset.mem_univ i)

theorem ustar_attained {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) : ∃ i, u i = ustar hm u := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Mfr m)).Nonempty) u
  exact ⟨i, by unfold ustar; rw [hi]⟩

theorem fold_max_eq {m : ℕ} (hm : 0 < m) (φ : ℝ) (u : Mfr m → ℝ) :
    Finset.univ.fold max φ u = max φ (ustar hm u) := by
  apply le_antisymm
  · rw [Finset.fold_max_le]
    exact ⟨le_max_left _ _, fun i _ => le_max_of_le_right (le_ustar hm u i)⟩
  · apply max_le
    · exact (Finset.le_fold_max φ).2 (Or.inl le_rfl)
    · obtain ⟨i, hi⟩ := ustar_attained hm u
      rw [Finset.le_fold_max]
      exact Or.inr ⟨i, Finset.mem_univ _, hi.symm.le⟩

noncomputable def wsel {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (φ : ℝ) : Option (Mfr m) → ℝ
  | none => if φ ≤ ustar hm u then 0 else 1
  | some i => if φ ≤ ustar hm u ∧ u i = ustar hm u then
      1 / ((Finset.univ.filter (fun k => u k = ustar hm u)).card : ℝ) else 0

noncomputable def wr {m : ℕ} (hm : 0 < m) (H L h l : ℝ) (β : BeliefSystem m) : PurchaseRule m :=
  fun t φ x b r o => wsel hm (uvec H L h l β t x b r) φ o

theorem card_argmax_pos {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) :
    (0 : ℝ) < ((Finset.univ.filter (fun k => u k = ustar hm u)).card : ℝ) := by
  obtain ⟨i, hi⟩ := ustar_attained hm u
  exact_mod_cast Finset.card_pos.2 ⟨i, by simp [hi]⟩

theorem wsel_nonneg {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (φ : ℝ) (o : Option (Mfr m)) :
    0 ≤ wsel hm u φ o := by
  cases o <;> simp only [wsel] <;> split_ifs <;> positivity

theorem wsel_sum {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (φ : ℝ) : ∑ o, wsel hm u φ o = 1 := by
  rw [Fintype.sum_option]
  simp only [wsel]
  by_cases hφ : φ ≤ ustar hm u
  · rw [if_pos hφ, zero_add]
    simp only [hφ, true_and]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := (card_argmax_pos hm u).ne'
    field_simp
  · rw [if_neg hφ]
    simp [hφ]

theorem wsel_pos_none {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (φ : ℝ) (h : 0 < wsel hm u φ none) :
    ustar hm u < φ := by
  simp only [wsel] at h
  split_ifs at h with hφ
  · exact absurd h (lt_irrefl 0)
  · exact not_le.mp hφ

theorem wsel_pos_some {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (φ : ℝ) (i : Mfr m)
    (h : 0 < wsel hm u φ (some i)) : φ ≤ ustar hm u ∧ u i = ustar hm u := by
  simp only [wsel] at h
  split_ifs at h with hc
  · exact hc
  · exact absurd h (lt_irrefl 0)

theorem wsel_none_zero {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (φ : ℝ) (h : φ ≤ ustar hm u) :
    wsel hm u φ none = 0 := by
  simp [wsel, h]

theorem wsel_some_zero {m : ℕ} (hm : 0 < m) (u : Mfr m → ℝ) (φ : ℝ) (i : Mfr m)
    (h : u i < ustar hm u) : wsel hm u φ (some i) = 0 := by
  simp only [wsel]
  rw [if_neg]
  rintro ⟨_, h2⟩
  linarith

theorem wsel_const {m : ℕ} (hm : 0 < m) (c φ : ℝ) (i : Mfr m) :
    wsel hm (fun _ => c) φ (some i) = (Set.Iic c).indicator (fun _ => 1 / (4 * (m : ℝ))) φ := by
  have hU : ustar hm (fun _ : Mfr m => c) = c := Finset.sup'_const _ c
  have hf : (Finset.univ.filter (fun k : Mfr m => c = ustar hm (fun _ : Mfr m => c))) =
      Finset.univ := Finset.filter_true_of_mem (fun _ _ => hU.symm)
  simp only [wsel, hU, and_true, Set.indicator, Set.mem_Iic]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl

theorem wr_opt {m : ℕ} (hm : 0 < m) (H L h l : ℝ) (β : BeliefSystem m) :
    IsOptimalPurchase H L h l β (wr hm H L h l β) := by
  intro t φ x b θ _
  refine ⟨fun o => wsel_nonneg hm (uvec H L h l β t x b (revealed b θ x)) φ o,
    wsel_sum hm (uvec H L h l β t x b (revealed b θ x)) φ, ?_, ?_⟩
  · intro o ho
    have hb : bestValue H L h l (β x b (revealed b θ x)) x t φ =
        max φ (ustar hm (uvec H L h l β t x b (revealed b θ x))) :=
      fold_max_eq hm φ (uvec H L h l β t x b (revealed b θ x))
    rw [hb]
    cases o with
    | none =>
      have := wsel_pos_none hm _ φ ho
      simp only [optionValue]
      rw [max_eq_left this.le]
    | some i =>
      obtain ⟨h1, h2⟩ := wsel_pos_some hm _ φ i ho
      simp only [optionValue]
      rw [max_eq_right h1]
      exact h2
  · rintro ⟨i, hi⟩
    exact wsel_none_zero hm (uvec H L h l β t x b (revealed b θ x)) φ
      (le_trans hi (le_ustar hm (uvec H L h l β t x b (revealed b θ x)) i))

def feeR (m : ℕ) : FeeRule m := fun _ _ _ => false

theorem wr_meas {m : ℕ} (hm : 0 < m) (H L h l : ℝ) (β : BeliefSystem m) :
    IsMeasurableRules (feeR m) (wr hm H L h l β) := by
  refine ⟨fun t x b r o => ?_, fun t x => ?_⟩
  · show Measurable (fun φ => wsel hm (uvec H L h l β t x b r) φ o)
    cases o with
    | none =>
      simp only [wsel]
      exact Measurable.ite measurableSet_Iic measurable_const measurable_const
    | some i =>
      simp only [wsel]
      exact Measurable.ite (measurableSet_Iic.inter (MeasurableSet.const _)) measurable_const
        measurable_const
  · simp [feeR]

/-! ### Fee optimality -/

theorem gv_bounds (H L h l : ℝ) (hLH : L ≤ H) (hlh : l ≤ h) (τ : MType) (t : Horiz) :
    L + l ≤ goodValue H L h l τ t ∧ goodValue H L h l τ t ≤ H + h := by
  obtain ⟨q, v⟩ := τ
  cases v <;> simp only [goodValue] <;> split_ifs <;> constructor <;> linarith

theorem expValue_bounds {m : ℕ} (H L h l : ℝ) (hLH : L ≤ H) (hlh : l ≤ h)
    {β' : (Mfr m → MType) → ℝ} (h0 : ∀ θ', 0 ≤ β' θ') (h1 : ∑ θ' ∈ Assignments m, β' θ' = 1)
    (i : Mfr m) (t : Horiz) :
    L + l ≤ expValue H L h l β' i t ∧ expValue H L h l β' i t ≤ H + h := by
  unfold expValue
  constructor
  · calc L + l = ∑ θ' ∈ Assignments m, β' θ' * (L + l) := by rw [← Finset.sum_mul, h1, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun θ' _ =>
          mul_le_mul_of_nonneg_left (gv_bounds H L h l hLH hlh _ t).1 (h0 θ'))
  · calc _ ≤ ∑ θ' ∈ Assignments m, β' θ' * (H + h) := Finset.sum_le_sum (fun θ' _ =>
          mul_le_mul_of_nonneg_left (gv_bounds H L h l hLH hlh _ t).2 (h0 θ'))
      _ = H + h := by rw [← Finset.sum_mul, h1, one_mul]

theorem fold_shift {m : ℕ} (φ D : ℝ) (hD : 0 ≤ D) (u u' : Mfr m → ℝ)
    (h : ∀ i, u' i ≤ u i + D) :
    Finset.univ.fold max φ u' ≤ Finset.univ.fold max φ u + D := by
  rw [Finset.fold_max_le]
  refine ⟨?_, fun i _ => ?_⟩
  · have h1 : φ ≤ Finset.univ.fold max φ u := (Finset.le_fold_max φ).2 (Or.inl le_rfl)
    linarith
  · have h1 : u i ≤ Finset.univ.fold max φ u :=
      (Finset.le_fold_max (u i)).2 (Or.inr ⟨i, Finset.mem_univ _, le_rfl⟩)
    linarith [h i]

theorem fee_opt {m : ℕ} (hm : 0 < m) (P H L h l : ℝ) (hLH : L ≤ H) (hlh : l ≤ h) :
    IsOptimalFee H L h l (bel hm P) ((H + h) - (L + l)) (feeR m) := by
  intro t φ x
  simp only [feeR, Bool.not_false]
  unfold feeValue
  simp only [↓reduceIte, Bool.false_eq_true, sub_zero]
  obtain ⟨p0, p1, -⟩ := prior0_prob hm P x
  have p0' : ∀ θ', 0 ≤ bel hm P x false noInfo θ' := p0
  have p1' : ∑ θ' ∈ Assignments m, bel hm P x false noInfo θ' = 1 := p1
  have key : ∀ θ' ∈ Assignments m,
      bestValue H L h l (bel hm P x true (revealed true θ' x)) x t φ ≤
        bestValue H L h l (bel hm P x false (revealed false θ' x)) x t φ + ((H + h) - (L + l)) := by
    intro θ' hθ'
    obtain ⟨q0, -, q1⟩ := bel_prob hm P x true hθ'
    obtain ⟨r0, -, r1⟩ := bel_prob hm P x false hθ'
    apply fold_shift φ _ (by linarith)
    intro i
    have e1 := (expValue_bounds H L h l hLH hlh q0 q1 i t).2
    have e2 := (expValue_bounds H L h l hLH hlh r0 r1 i t).1
    simp only [utility]
    linarith
  have hsum : ∑ θ' ∈ Assignments m, bel hm P x false noInfo θ' *
        bestValue H L h l (bel hm P x true (revealed true θ' x)) x t φ ≤
      ∑ θ' ∈ Assignments m, bel hm P x false noInfo θ' *
        bestValue H L h l (bel hm P x false (revealed false θ' x)) x t φ + ((H + h) - (L + l)) := by
    calc _ ≤ ∑ θ' ∈ Assignments m, (bel hm P x false noInfo θ' *
            bestValue H L h l (bel hm P x false (revealed false θ' x)) x t φ +
            bel hm P x false noInfo θ' * ((H + h) - (L + l))) :=
          Finset.sum_le_sum (fun θ' hθ' => by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (key θ' hθ') (p0' θ'))
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, p1', one_mul]
  linarith

/-! ### Vendor -/

def feasLo {m : ℕ} (θ : Mfr m → MType) (s σ' : Mfr m → ℝ) : Prop :=
  ∀ i, (θ i).2 = .lo → 0 ≤ σ' i ∧ σ' i ≤ s i

def optLo {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (θ : Mfr m → MType) (Ψ s σ : Mfr m → ℝ) : Prop :=
  ∀ σ', feasLo θ s σ' → vendorProfit γ cl θ .lo Ψ σ' ≤ vendorProfit γ cl θ .lo Ψ σ

open Classical in
noncomputable def loPart {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (θ : Mfr m → MType) (Ψ s : Mfr m → ℝ) :
    Mfr m → ℝ :=
  if optLo γ cl θ Ψ s s then s else
    if hx : ∃ σ : Mfr m → ℝ, (∀ i, 0 ≤ σ i ∧ σ i ≤ s i) ∧ optLo γ cl θ Ψ s σ
    then Classical.choose hx else 0

noncomputable def vnd {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) : VendorRule m := fun θ Ψ s i =>
  if (θ i).2 = .hi then (if γ ≤ Ψ i then s i else 0) else loPart γ cl θ Ψ s i

theorem vp_congr {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (θ : Mfr m → MType) (v : Vert) (Ψ : Mfr m → ℝ)
    {σ σ' : Mfr m → ℝ} (h : ∀ i, (θ i).2 = v → σ i = σ' i) :
    vendorProfit γ cl θ v Ψ σ = vendorProfit γ cl θ v Ψ σ' := by
  unfold vendorProfit
  congr 1
  · exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_filter.1 hi).2])
  · congr 1
    exact Finset.sum_congr rfl (fun i hi => h i (Finset.mem_filter.1 hi).2)

theorem vp_hi {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (θ : Mfr m → MType) (Ψ σ : Mfr m → ℝ) :
    vendorProfit γ cl θ .hi Ψ σ =
      ∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = .hi), (Ψ i - γ) * σ i := by
  simp only [vendorProfit, vendorCost, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]

theorem exists_optLo {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (hcont : ContinuousOn cl (Set.Ici 0))
    (θ : Mfr m → MType) (Ψ s : Mfr m → ℝ) (hs : ∀ i, 0 ≤ s i) :
    ∃ σ, (∀ i, 0 ≤ σ i ∧ σ i ≤ s i) ∧ optLo γ cl θ Ψ s σ := by
  set K : Set (Mfr m → ℝ) := Set.pi Set.univ (fun i => Set.Icc 0 (s i)) with hK
  have hKc : IsCompact K := isCompact_univ_pi (fun i => isCompact_Icc)
  have hKn : K.Nonempty := ⟨0, fun i _ => ⟨le_rfl, hs i⟩⟩
  have hcontK : ContinuousOn (fun σ => vendorProfit γ cl θ .lo Ψ σ) K := by
    show ContinuousOn (fun σ : Mfr m → ℝ =>
      ∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = .lo), Ψ i * σ i -
        cl (∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = .lo), σ i)) K
    apply ContinuousOn.sub
    · exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))).continuousOn
    · refine ContinuousOn.comp (g := cl)
        (f := fun σ : Mfr m → ℝ => ∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = .lo), σ i)
        hcont (continuous_finsetSum _ (fun i _ => continuous_apply i)).continuousOn ?_
      intro σ hσ
      exact Finset.sum_nonneg (fun i _ => (hσ i (Set.mem_univ i)).1)
  obtain ⟨σ0, hσ0, hmax⟩ := hKc.exists_isMaxOn hKn hcontK
  refine ⟨σ0, fun i => hσ0 i (Set.mem_univ i), fun σ' hσ' => ?_⟩
  let σ'' : Mfr m → ℝ := fun i => if (θ i).2 = .lo then σ' i else 0
  have h1 : vendorProfit γ cl θ .lo Ψ σ' = vendorProfit γ cl θ .lo Ψ σ'' :=
    vp_congr γ cl θ .lo Ψ (fun i hv => by simp [σ'', hv])
  have h2 : σ'' ∈ K := fun i _ => by
    by_cases hv : (θ i).2 = .lo
    · simp only [σ'', hv, ↓reduceIte]; exact hσ' i hv
    · simp only [σ'', hv, ↓reduceIte]; exact ⟨le_rfl, hs i⟩
  rw [h1]
  exact hmax h2

theorem vnd_opt {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (hcont : ContinuousOn cl (Set.Ici 0)) :
    IsOptimalVendor γ cl (vnd (m := m) γ cl) := by
  intro θ _ Ψ s _ hs
  have hex := exists_optLo γ cl hcont θ Ψ s hs
  have hlo : (∀ i, 0 ≤ loPart γ cl θ Ψ s i ∧ loPart γ cl θ Ψ s i ≤ s i) ∧
      optLo γ cl θ Ψ s (loPart γ cl θ Ψ s) := by
    unfold loPart
    by_cases h1 : optLo γ cl θ Ψ s s
    · rw [if_pos h1]; exact ⟨fun i => ⟨hs i, le_rfl⟩, h1⟩
    · rw [if_neg h1, dif_pos hex]; exact Classical.choose_spec hex
  refine ⟨fun i => ?_, fun v σ' hσ' => ?_⟩
  · unfold vnd
    split_ifs
    · exact ⟨hs i, le_rfl⟩
    · exact ⟨le_rfl, hs i⟩
    · exact hlo.1 i
  · cases v with
    | hi =>
      rw [vp_hi, vp_hi]
      apply Finset.sum_le_sum
      intro i hiF
      have hv := (Finset.mem_filter.1 hiF).2
      obtain ⟨a1, a2⟩ := hσ' i hv
      simp only [vnd, hv, ↓reduceIte]
      split_ifs with hg
      · exact mul_le_mul_of_nonneg_left a2 (by linarith)
      · nlinarith
    | lo =>
      rw [vp_congr γ cl θ .lo Ψ (σ' := loPart γ cl θ Ψ s) (σ := vnd γ cl θ Ψ s)
        (fun i hv => by simp [vnd, hv])]
      exact hlo.2 σ' hσ'

theorem vp_lo_formula {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (θ : Mfr m → MType) (Ψ σ : Mfr m → ℝ)
    (ψ : ℝ) (j : Mfr m) (hj : (θ j).2 = .lo) (hΨ : ∀ i, (θ i).2 = .lo → i ≠ j → Ψ i = ψ) :
    vendorProfit γ cl θ .lo Ψ σ =
      ψ * (∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = .lo), σ i) + (Ψ j - ψ) * σ j -
        cl (∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = .lo), σ i) := by
  show ∑ i ∈ _, Ψ i * σ i - cl _ = _
  congr 1
  have : ∀ i ∈ Finset.univ.filter (fun i => (θ i).2 = .lo),
      Ψ i * σ i = ψ * σ i + (if i = j then (Ψ j - ψ) * σ j else 0) := by
    intro i hi
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; ring
    · rw [hΨ i (Finset.mem_filter.1 hi).2 hij, if_neg hij, add_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  simp [hj]

theorem conv_le (cl cl' : ℝ → ℝ)
    (hd : ∀ x, 0 ≤ x → HasDerivWithinAt cl (cl' x) (Set.Ici 0) x)
    (hmono : StrictMonoOn cl' (Set.Ici 0)) {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S) :
    cl S - cl T ≤ cl' S * (S - T) := by
  rcases hTS.lt_or_eq with hlt | heq
  · have hcont : ContinuousOn cl (Set.Icc T S) := fun x hx =>
      ((hd x (hT.trans hx.1)).continuousWithinAt).mono (fun y hy => hT.trans hy.1)
    have hder : ∀ x ∈ Set.Ioo T S, HasDerivAt cl (cl' x) x := fun x hx =>
      (hd x (hT.trans hx.1.le)).hasDerivAt (Ici_mem_nhds (hT.trans_lt hx.1))
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope cl cl' hlt hcont hder
    have hlt2 : cl' c < cl' S :=
      hmono (Set.mem_Ici.2 (hT.trans hc.1.le)) (Set.mem_Ici.2 (hT.trans hlt.le)) hc.2
    rw [eq_div_iff (by linarith)] at hcd
    nlinarith
  · subst heq; simp

theorem exists_eps (cl : ℝ → ℝ) {ψ Ψ' S a : ℝ} (hS : 0 < S) (ha : 0 < a)
    (hd : HasDerivWithinAt cl ψ (Set.Ici 0) S) (hlt : Ψ' < ψ) :
    ∃ ε, 0 < ε ∧ ε ≤ a ∧ ε < S ∧ Ψ' * ε < cl S - cl (S - ε) := by
  have hD : HasDerivAt cl ψ S := hd.hasDerivAt (Ici_mem_nhds hS)
  have ht := hD.tendsto_slope_zero_left
  have hev1 := ht.eventually (lt_mem_nhds hlt)
  have hev2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0), t ∈ Set.Ioo (-(min a (S / 2))) 0 :=
    Ioo_mem_nhdsLT (by simp [ha, hS])
  obtain ⟨t, h1, h2⟩ := (hev1.and hev2).exists
  have ht0 : t < 0 := h2.2
  have htm : -(min a (S / 2)) < t := h2.1
  have hma := min_le_left a (S / 2)
  have hms := min_le_right a (S / 2)
  rw [smul_eq_mul] at h1
  have htne : t ≠ 0 := ht0.ne
  have key : t * (t⁻¹ * (cl (S + t) - cl S)) = cl (S + t) - cl S := by
    rw [← mul_assoc, mul_inv_cancel₀ htne, one_mul]
  have h3 := mul_lt_mul_of_neg_left h1 ht0
  rw [key] at h3
  refine ⟨-t, by linarith, by linarith, by linarith, ?_⟩
  rw [show S - -t = S + t by ring]
  linarith

theorem vnd_full {m : ℕ} (γ : ℝ) (cl cl' : ℝ → ℝ)
    (hd : ∀ x, 0 ≤ x → HasDerivWithinAt cl (cl' x) (Set.Ici 0) x)
    (hmono : StrictMonoOn cl' (Set.Ici 0)) (θ : Mfr m → MType) (Ψ s : Mfr m → ℝ) (i : Mfr m)
    (hhi : (θ i).2 = .hi → Ψ i = γ)
    (hΨ : ∀ k, (θ k).2 = .lo →
      Ψ k = cl' (∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), s k)) :
    vnd γ cl θ Ψ s i = s i := by
  unfold vnd
  split_ifs with h1 h2
  · rfl
  · exact absurd (le_of_eq (hhi h1).symm) h2
  · have hlo : (θ i).2 = .lo := by
      revert h1; cases (θ i).2 <;> simp
    have hopt : optLo γ cl θ Ψ s s := by
      intro σ' hσ'
      rw [vp_lo_formula γ cl θ Ψ σ' _ i hlo (fun k hk _ => hΨ k hk),
        vp_lo_formula γ cl θ Ψ s _ i hlo (fun k hk _ => hΨ k hk), hΨ i hlo, sub_self, zero_mul,
        zero_mul, add_zero, add_zero]
      have hT0 : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), σ' k :=
        Finset.sum_nonneg (fun k hk => (hσ' k (Finset.mem_filter.1 hk).2).1)
      have hTS : ∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), σ' k ≤
          ∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), s k :=
        Finset.sum_le_sum (fun k hk => (hσ' k (Finset.mem_filter.1 hk).2).2)
      have := conv_le cl cl' hd hmono hT0 hTS
      set S := ∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), s k
      set T := ∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), σ' k
      have e : cl' S * S - cl S - (cl' S * T - cl T) = cl' S * (S - T) - (cl S - cl T) := by ring
      linarith
    unfold loPart
    rw [if_pos hopt]

theorem vnd_refuse {m : ℕ} (γ : ℝ) (cl cl' : ℝ → ℝ)
    (hd : ∀ x, 0 ≤ x → HasDerivWithinAt cl (cl' x) (Set.Ici 0) x)
    (hmono : StrictMonoOn cl' (Set.Ici 0)) (θ : Mfr m → MType) (Ψ s : Mfr m → ℝ) (j : Mfr m)
    (hj : (θ j).2 = .lo) (hs : ∀ k, 0 ≤ s k) (hsj : 0 < s j)
    (hΨ : ∀ k, (θ k).2 = .lo → k ≠ j →
      Ψ k = cl' (∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), s k))
    (hlt : Ψ j < cl' (∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), s k)) :
    vnd γ cl θ Ψ s j ≠ s j := by
  set F := Finset.univ.filter (fun k => (θ k).2 = Vert.lo) with hF
  set S := ∑ k ∈ F, s k with hS
  have hjF : j ∈ F := by simp [hF, hj]
  have hSj : s j ≤ S := Finset.single_le_sum (fun k _ => hs k) hjF
  have hSpos : 0 < S := lt_of_lt_of_le hsj hSj
  obtain ⟨ε, hε0, hεa, _, hεgain⟩ := exists_eps cl hSpos hsj (hd S hSpos.le) hlt
  set σ'' : Mfr m → ℝ := fun k => s k - (if k = j then ε else 0) with hσ''
  have hfe : feasLo θ s σ'' := by
    intro k _
    simp only [σ'']
    split_ifs with hk
    · subst hk; constructor <;> linarith
    · constructor <;> linarith [hs k]
  have hsum'' : ∑ k ∈ F, σ'' k = S - ε := by
    simp only [σ'', Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hjF, hS]
  have hσj : σ'' j = s j - ε := by simp [σ'']
  have hgain : vendorProfit γ cl θ .lo Ψ σ'' - vendorProfit γ cl θ .lo Ψ s =
      cl S - cl (S - ε) - Ψ j * ε := by
    rw [vp_lo_formula γ cl θ Ψ σ'' (cl' S) j hj hΨ, vp_lo_formula γ cl θ Ψ s (cl' S) j hj hΨ]
    rw [hsum'', hσj]
    ring
  have hle : ∀ σ, feasLo θ s σ → σ j = s j →
      vendorProfit γ cl θ .lo Ψ σ ≤ vendorProfit γ cl θ .lo Ψ s := by
    intro σ hσ hσj'
    have hT0 : 0 ≤ ∑ k ∈ F, σ k :=
      Finset.sum_nonneg (fun k hk => (hσ k (Finset.mem_filter.1 hk).2).1)
    have hTS : ∑ k ∈ F, σ k ≤ S :=
      Finset.sum_le_sum (fun k hk => (hσ k (Finset.mem_filter.1 hk).2).2)
    have hc := conv_le cl cl' hd hmono hT0 hTS
    have e : vendorProfit γ cl θ .lo Ψ s - vendorProfit γ cl θ .lo Ψ σ =
        cl' S * (S - ∑ k ∈ F, σ k) - (cl S - cl (∑ k ∈ F, σ k)) := by
      rw [vp_lo_formula γ cl θ Ψ σ (cl' S) j hj hΨ, vp_lo_formula γ cl θ Ψ s (cl' S) j hj hΨ, hσj']
      ring
    linarith
  have hvj : vnd γ cl θ Ψ s j = loPart γ cl θ Ψ s j := by simp [vnd, hj]
  rw [hvj]
  unfold loPart
  split_ifs with h1 h2
  · have := h1 σ'' hfe
    linarith
  · intro heq
    obtain ⟨hb, hopt⟩ := Classical.choose_spec h2
    have h3 := hopt σ'' hfe
    have h4 := hle _ (fun k _ => hb k) heq
    linarith
  · show (0 : ℝ) ≠ s j
    exact hsj.ne

/-! ### Demand -/

theorem uvec_onpath {m : ℕ} (hm : 0 < m) (P H L h l : ℝ) (t : Horiz) :
    uvec H L h l (bel hm P) t (x0 m P) false noInfo = fun _ => (H + L + h + l) / 2 - P := by
  funext k
  have e : bel hm P (x0 m P) false noInfo = unif m := by
    funext θ'
    simp only [bel, Bool.false_eq_true, ↓reduceIte, prior0]
  show expValue H L h l (bel hm P (x0 m P) false noInfo) k t - (x0 m P).2 k = _
  rw [e, expValue_unif hm]
  rfl

theorem sOf_onpath {m : ℕ} (hm : 0 < m) (ν : Measure ℝ) (P ψ γ H L h l : ℝ)
    (θ : Mfr m → MType) (i : Mfr m) :
    sOf ν (feeR m) (wr hm H L h l (bel hm P)) θ (onPath (actP P ψ γ) θ) i =
      ν.real (Set.Iic ((H + L + h + l) / 2 - P)) / (4 * m) := by
  unfold sOf demand
  rw [hist_onPath]
  simp only [feeR, revealed_false, wr, uvec_onpath hm, wsel_const hm,
    integral_indicator_const _ measurableSet_Iic, sum_horiz, smul_eq_mul]
  ring

theorem dev_eq {m : ℕ} (hm : 0 < m) (P : ℝ) (x : Hist m) (i : Mfr m)
    (hi : ¬ (x.1 i = true ∧ x.2 i = P)) (hothers : ∀ k, k ≠ i → x.1 k = true ∧ x.2 k = P) :
    dev hm P x = i := by
  unfold dev
  rw [dif_pos ⟨i, hi⟩]
  by_contra hne
  exact (Classical.choose_spec (⟨i, hi⟩ : ∃ j, ¬ (x.1 j = true ∧ x.2 j = P))) (hothers _ hne)

theorem expValue_pun {m : ℕ} (hm : 0 < m) (H L h l : ℝ) (j k : Mfr m) (t : Horiz) :
    expValue H L h l (pun hm j) k t =
      goodValue H L h l (th1 hm j k) t / 2 + goodValue H L h l (th2 hm j k) t / 2 :=
  sum_pun hm j (fun θ' => goodValue H L h l (θ' k) t)

theorem sOf_dev_zero {m : ℕ} (hm : 0 < m) (ν : Measure ℝ) (P ψ γ H L h l : ℝ)
    (hpun : P < (H - L) / 2 + h - l) (θ : Mfr m → MType) (i : Mfr m) (a' : Bool) (P' Ψ' : ℝ)
    (hP' : 0 ≤ P') (hdev : ¬ (a' = true ∧ P' = P)) :
    sOf ν (feeR m) (wr hm H L h l (bel hm P)) θ
      (Function.update (onPath (actP P ψ γ) θ) i (a', P', Ψ')) i = 0 := by
  set x' := histOf (Function.update (onPath (actP P ψ γ) θ) i (a', P', Ψ')) with hx'
  have hx1 : ∀ k, k ≠ i → x'.1 k = true ∧ x'.2 k = P := by
    intro k hk
    simp [hx', histOf, Function.update_of_ne hk, onPath, actP]
  have hxi : x'.1 i = a' ∧ x'.2 i = P' := by simp [hx', histOf]
  have hne : x' ≠ x0 m P := by
    intro h
    apply hdev
    rw [← hxi.1, ← hxi.2, h]
    simp [x0]
  have hdv : dev hm P x' = i := dev_eq hm P x' i (by rw [hxi.1, hxi.2]; exact hdev) hx1
  have hpr : bel hm P x' false noInfo = pun hm i := by
    funext θ'
    simp only [bel, Bool.false_eq_true, ↓reduceIte, prior0, if_neg hne, hdv]
  have hzero : ∀ t φ, wsel hm (uvec H L h l (bel hm P) t x' false noInfo) φ (some i) = 0 := by
    intro t φ
    apply wsel_some_zero
    obtain ⟨k, hki, hk1, hk2⟩ := rival hm i t
    have hui : uvec H L h l (bel hm P) t x' false noInfo i = (H + L) / 2 + l - P' := by
      simp only [uvec, utility, hpr, expValue_pun, th1_j, th2_j, hxi.2]
      cases t <;> simp [goodValue] <;> ring
    have huk : uvec H L h l (bel hm P) t x' false noInfo k = H + h - P := by
      simp only [uvec, utility, hpr, expValue_pun, hk1, hk2, (hx1 k hki).2]
      (try simp [goodValue]) <;> (try ring)
    have := le_ustar hm (uvec H L h l (bel hm P) t x' false noInfo) k
    rw [hui]
    rw [huk] at this
    linarith
  unfold sOf demand
  rw [← hx']
  simp only [feeR, revealed_false, wr, hzero, integral_zero, Finset.sum_const_zero, mul_zero]

theorem hist_same {m : ℕ} (P ψ γ : ℝ) (θ : Mfr m → MType) (i : Mfr m) (Ψ' : ℝ) :
    histOf (Function.update (onPath (actP P ψ γ) θ) i (true, P, Ψ')) = x0 m P := by
  simp only [histOf, x0]
  congr 1 <;> funext k <;> by_cases hk : k = i <;> simp [hk, onPath, actP, Function.update_apply]

/-! ### Main construction -/

theorem main {m : ℕ} (hm : 2 ≤ m) {L h l γ : ℝ} (hL : 0 ≤ L) (hl : 0 ≤ l) (hlh : l < h)
    (hγ : 0 < γ) (χ : Mfr m → ℝ) (hχ : ∀ i, 0 < χ i)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (cl cl' : ℝ → ℝ)
    (hcl : StrictMonoOn cl (Set.Ici 0)) :
    ∃ Δbar : ℝ, ∀ Δ : ℝ, Δbar < Δ → Assumption1 ν γ (L + Δ) L h l cl cl' →
      ∃ (κ : ℝ) (τ : Mfr m → ℝ) (act : Strategy m) (β : BeliefSystem m) (fee : FeeRule m)
        (w : PurchaseRule m) (vend : VendorRule m),
        0 ≤ κ ∧ (∀ i, 0 ≤ τ i) ∧
        IsTransferEquilibrium ν (L + Δ) L h l γ cl χ κ τ act β fee w vend ∧
        SelfFinancing ν κ τ act fee ∧ FullAdoption act := by
  have hm0 : 0 < m := by omega
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨xh, hxh⟩ : ∃ x : ℝ, (1 : ℝ) / 2 ≤ ν.real (Set.Iic x) := by
    obtain ⟨x, hx⟩ := ((ProbabilityTheory.tendsto_cdf_atTop ν).eventually
      (lt_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num))).exists
    exact ⟨x, by rw [ProbabilityTheory.cdf_eq_real] at hx; exact hx.le⟩
  have hne : (Finset.univ : Finset (Mfr m)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set X : ℝ := ∑ i, χ i with hX
  have hXpos : 0 < X := Finset.sum_pos (fun i _ => hχ i) hne
  have hχX : ∀ i, χ i ≤ X := fun i =>
    Finset.single_le_sum (fun j _ => (hχ j).le) (Finset.mem_univ i)
  set C0 : ℝ := |γ| + |cl' (1 / 2)| with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  refine ⟨4 * (C0 + 8 * m * X) + 4 * |xh|, fun Δ hΔ hA => ?_⟩
  obtain ⟨_, hd, hmono, _, _⟩ := hA
  have hcont : ContinuousOn cl (Set.Ici 0) := fun x hx => (hd x hx).continuousWithinAt
  have hxa := abs_nonneg xh
  have h8 : 0 ≤ 8 * (m : ℝ) * X := by positivity
  have hΔpos : 0 < Δ := by linarith
  set P : ℝ := Δ / 4 with hP
  set U0 : ℝ := ((L + Δ) + L + h + l) / 2 - P with hU0
  set νU : ℝ := ν.real (Set.Iic U0) with hνU
  have hPbig : C0 + 8 * m * X + |xh| < P := by rw [hP]; linarith
  have hU0P : P ≤ U0 := by rw [hU0, hP]; linarith
  have hνU1 : νU ≤ 1 := measureReal_le_one
  have hνUh : 1 / 2 ≤ νU :=
    le_trans hxh (measureReal_mono (Set.Iic_subset_Iic.2 (by linarith [le_abs_self xh])))
  set s0 : ℝ := νU / (4 * m) with hs0
  set Sv : ℝ := νU / 2 with hSv
  set ψ : ℝ := cl' Sv with hψ
  have hSv0 : 0 < Sv := by rw [hSv]; linarith
  have hψle : ψ ≤ cl' (1 / 2) :=
    hmono.monotoneOn (Set.mem_Ici.2 hSv0.le) (Set.mem_Ici.2 (by norm_num)) (by rw [hSv]; linarith)
  have hψpos : 0 < ψ := by
    have h1 := conv_le cl cl' hd hmono (le_refl 0) hSv0.le
    have h2 : cl 0 < cl Sv := hcl (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hSv0.le) hSv0
    rw [sub_zero] at h1
    by_contra hc
    push_neg at hc
    nlinarith
  have hs0pos : 1 / (8 * m) ≤ s0 := by
    rw [hs0, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hs0p : 0 < s0 := lt_of_lt_of_le (by positivity) hs0pos
  have hmargin : ∀ C, C ≤ C0 → X ≤ (P - C) * s0 := by
    intro C hC
    have h1 : 8 * m * X ≤ P - C := by linarith
    calc X = (8 * m * X) * (1 / (8 * m)) := by field_simp
      _ ≤ (P - C) * s0 := mul_le_mul h1 hs0pos (by positivity) (by linarith)
  have hγC : γ ≤ C0 := by have := le_abs_self γ; have := abs_nonneg (cl' (1 / 2)); linarith
  have hψC : ψ ≤ C0 := by have := le_abs_self (cl' (1 / 2)); have := abs_nonneg γ; linarith
  have hsOn : ∀ θ i, sOf ν (feeR m) (wr hm0 (L + Δ) L h l (bel hm0 P)) θ
      (onPath (actP P ψ γ) θ) i = s0 := by
    intro θ i
    rw [sOf_onpath]
  have hsumF : ∀ θ, θ ∈ Assignments m →
      ∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), (fun _ : Mfr m => s0) k = Sv := by
    intro θ hθ
    rw [Finset.sum_const, card_lo hθ, nsmul_eq_mul, hs0, hSv]
    push_cast
    field_simp
    ring
  have hpun : P < ((L + Δ) - L) / 2 + h - l := by rw [hP]; linarith
  refine ⟨(L + Δ + h) - (L + l), fun _ => 0, actP P ψ γ, bel hm0 P, feeR m,
    wr hm0 (L + Δ) L h l (bel hm0 P), vnd γ cl, by linarith, fun _ => le_rfl,
    ⟨bel_consistent hm0 P ψ γ, wr_opt hm0 _ _ _ _ _,
      fee_opt hm0 P (L + Δ) L h l (by linarith) hlh.le, wr_meas hm0 _ _ _ _ _,
      vnd_opt γ cl hcont, fun θ hθ => ⟨?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · intro i
    simp only [onPath, actP]
    refine ⟨by linarith, ?_⟩
    split_ifs <;> linarith
  · intro i
    unfold fulfilled sigmaOf
    have hsv : sOf ν (feeR m) (wr hm0 (L + Δ) L h l (bel hm0 P)) θ (onPath (actP P ψ γ) θ) =
        fun _ => s0 := funext (hsOn θ)
    rw [hsv]
    apply vnd_full γ cl cl' hd hmono
    · intro hhi
      show (if (θ i).2 = .hi then γ else ψ) = γ
      rw [if_pos hhi]
    · intro k hk
      show (if (θ k).2 = .hi then γ else ψ) =
        cl' (∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), (fun _ : Mfr m => s0) k)
      rw [hsumF θ hθ, if_neg (by rw [hk]; decide)]
  · intro i a' P' Ψ' hP' hΨ' hful
    set Ψi : ℝ := if (θ i).2 = .hi then γ else ψ with hΨi
    have hpay0 : payoff ν (feeR m) (wr hm0 (L + Δ) L h l (bel hm0 P)) χ (fun _ => 0) θ
        (onPath (actP P ψ γ) θ) i = (P - Ψi) * s0 - χ i := by
      simp only [payoff, hsOn]
      simp only [onPath, actP, ↓reduceIte, hΨi]
      ring
    have hon : 0 ≤ (P - Ψi) * s0 - χ i := by
      have := hχX i
      rw [hΨi]
      split_ifs
      · linarith [hmargin γ hγC]
      · linarith [hmargin ψ hψC]
    rw [hpay0]
    by_cases hsame : a' = true ∧ P' = P
    · obtain ⟨ha, hpp⟩ := hsame
      subst ha
      rw [hpp] at hful ⊢
      have hs' : sOf ν (feeR m) (wr hm0 (L + Δ) L h l (bel hm0 P)) θ
          (Function.update (onPath (actP P ψ γ) θ) i (true, P, Ψ')) = fun _ => s0 := by
        funext k
        rw [← hsOn θ k]
        unfold sOf
        rw [hist_same, hist_onPath]
      have hpay1 : payoff ν (feeR m) (wr hm0 (L + Δ) L h l (bel hm0 P)) χ (fun _ => 0) θ
          (Function.update (onPath (actP P ψ γ) θ) i (true, P, Ψ')) i =
            (P - Ψ') * s0 - χ i := by
        simp only [payoff, hs', Function.update_self, ↓reduceIte]
        ring
      rw [hpay1]
      by_cases hΨle : Ψi ≤ Ψ'
      · nlinarith
      · exfalso
        unfold fulfilled sigmaOf at hful
        rw [hs'] at hful
        by_cases hv : (θ i).2 = .hi
        · have hΨγ : Ψi = γ := by rw [hΨi, if_pos hv]
          rw [hΨγ] at hΨle
          simp only [vnd, hv, ↓reduceIte, Function.update_self, if_neg hΨle] at hful
          linarith
        · have hlo : (θ i).2 = .lo := by revert hv; cases (θ i).2 <;> simp
          have hΨψ : Ψi = ψ := by rw [hΨi, if_neg hv]
          rw [hΨψ] at hΨle
          refine vnd_refuse γ cl cl' hd hmono θ _ (fun _ => s0) i hlo (fun _ => hs0p.le) hs0p
            ?_ ?_ hful
          · intro k hk hki
            show (Function.update (onPath (actP P ψ γ) θ) i (true, P, Ψ') k).2.2 =
              cl' (∑ k ∈ Finset.univ.filter (fun k => (θ k).2 = .lo), (fun _ : Mfr m => s0) k)
            rw [hsumF θ hθ, Function.update_of_ne hki]
            show (if (θ k).2 = .hi then γ else ψ) = _
            rw [if_neg (by rw [hk]; decide)]
          · rw [hsumF θ hθ]
            simp only [Function.update_self]
            linarith
    · have hz := sOf_dev_zero hm0 ν P ψ γ (L + Δ) L h l hpun θ i a' P' Ψ' hP' hsame
      simp only [payoff, hz, mul_zero, sub_zero, Function.update_self]
      cases a' <;> simp <;> linarith [hχ i]
  · intro θ _
    simp [feeMass, feeR]
  · intro θ _ i
    rfl

end E78PB

open PermBlockchain.Transfers in
theorem solution {m : ℕ} (hm : 2 ≤ m)
    {L h l γ : ℝ} (hL : 0 ≤ L) (hl : 0 ≤ l) (hlh : l < h) (hγ : 0 < γ)
    (χ : Mfr m → ℝ) (hχ : ∀ i, 0 < χ i)
    (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
    [MeasureTheory.NullSingletonClass ν] (hν : ν (Set.Iio 0) = 0)
    (cl cl' : ℝ → ℝ) (hcl : StrictMonoOn cl (Set.Ici 0)) :
    ∃ Δbar : ℝ, ∀ Δ : ℝ, Δbar < Δ → Assumption1 ν γ (L + Δ) L h l cl cl' →
      ∃ (κ : ℝ) (τ : Mfr m → ℝ) (act : Strategy m) (β : BeliefSystem m) (fee : FeeRule m)
        (w : PurchaseRule m) (vend : VendorRule m),
        0 ≤ κ ∧ (∀ i, 0 ≤ τ i) ∧
        IsTransferEquilibrium ν (L + Δ) L h l γ cl χ κ τ act β fee w vend ∧
        SelfFinancing ν κ τ act fee ∧ FullAdoption act := by
  exact E78PB.main hm hL hl hlh hγ χ hχ ν cl cl' hcl
