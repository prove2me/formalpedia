-- Prove2me | solution 1 for SinkReset.Plan.closed_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:03.635382+00:00
-- url     : https://prove2.me/submissions/54925000-e8fa-4af1-b02e-c60833206c00

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_append
public import Theorems.Thm_SinkReset_Plan_word_append
public import Theorems.Thm_SinkReset_Plan_wins_mono
public import Theorems.Thm_SinkReset_Plan_lift_word
public import Theorems.Thm_SinkReset_Plan_wins_push
public import Theorems.Thm_SinkReset_Plan_wins_pull
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
private theorem push_act (φ : Fin n → Fin m)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (a q) = τ a (φ q))
    (u : List (Letter n)) (hu : A.IsWord u) (q : Fin n) :
    φ (act u q) = act (u.map τ) (φ q) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    have ha : a ∈ A.letters := hu a List.mem_cons_self
    change φ (act u (a q)) = act (u.map τ) (τ a (φ q))
    rw [ih (fun c hc => hu c (List.mem_cons_of_mem _ hc)), hcomm a ha]
private theorem pull_act (φ : Fin m → Fin n)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (τ a q) = a (φ q))
    (u : List (Letter n)) (hu : A.IsWord u) (q : Fin m) :
    φ (act (u.map τ) q) = act u (φ q) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    have ha : a ∈ A.letters := hu a List.mem_cons_self
    change φ (act (u.map τ) (τ a q)) = act u (a (φ q))
    rw [ih (fun c hc => hu c (List.mem_cons_of_mem _ hc)), hcomm a ha]
end Transport
private theorem emb_of_finset {n : ℕ} [NeZero n] (X : Finset (Fin n)) (h0 : (0 : Fin n) ∈ X)
    (p : ℕ) (hp : X.card = p + 1) :
    ∃ e : Fin (p + 1) → Fin n, Function.Injective e ∧ e 0 = 0 ∧ ∀ x, x ∈ X ↔ ∃ i, e i = x := by
  refine ⟨X.orderEmbOfFin hp, (X.orderEmbOfFin hp).injective, ?_, ?_⟩
  · have h1 := Finset.orderEmbOfFin_zero hp (Nat.succ_pos p)
    have h2 : X.min' (Finset.card_pos.mp (hp.symm ▸ Nat.succ_pos p)) ≤ 0 := Finset.min'_le X 0 h0
    have h3 : (X.min' (Finset.card_pos.mp (hp.symm ▸ Nat.succ_pos p))) = 0 :=
      le_antisymm h2 (Fin.zero_le _)
    rw [← h3, ← h1]
    rfl
  · intro x
    have := congrArg (x ∈ ·) (Finset.range_orderEmbOfFin X hp)
    simp only [Set.mem_range, Finset.mem_coe] at this
    exact Iff.of_eq this.symm
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {n k : ℕ} [NeZero n] (A : Automaton n) (hk : 1 ≤ k)
    (hA : A.IsAk k) (R : Finset (Fin n)) (hz : 0 ∈ R)
    (hcard : 2 ≤ R.card) (hproper : R.card < n)
    (hclosed : ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R) :
    ∃ c d : ℕ, 1 ≤ c ∧ 1 ≤ d ∧ c + d + 1 = n ∧
      d + 1 = R.card ∧
      ∃ B : Automaton (c + 1), ∃ C : Automaton (d + 1),
        B.IsAk k ∧ C.IsAk k ∧
        ∀ u v, B.IsReset u → C.IsReset v →
          ∃ w, A.IsReset w ∧ w.length = u.length + v.length := by
  classical
  set c := n - R.card with hc
  set d := R.card - 1 with hd
  refine ⟨c, d, by omega, by omega, by omega, by omega, ?_⟩
  -- the subautomaton on `R`
  obtain ⟨eC, heCi, heC0, heCr⟩ := emb_of_finset R hz d (by omega)
  set iC := Function.invFun eC with hiC
  have hiCl : ∀ i, iC (eC i) = i := Function.leftInverse_invFun heCi
  have hiCr : ∀ x ∈ R, eC (iC x) = x := fun x hx => Function.invFun_eq ((heCr x).1 hx)
  have heCR : ∀ i, eC i ∈ R := fun i => (heCr _).2 ⟨i, rfl⟩
  let τC : Letter n → Letter (d + 1) := fun a i => iC (a (eC i))
  let C : Automaton (d + 1) :=
    { letters := τC '' A.letters
      sink_fixed := by
        rintro _ ⟨a, ha, rfl⟩
        change iC (a (eC 0)) = 0
        rw [heC0, A.sink_fixed a ha, ← heC0, hiCl] }
  have hCl : ∀ b, b ∈ C.letters ↔ ∃ a ∈ A.letters, τC a = b := fun b => Iff.rfl
  have hCc : ∀ a ∈ A.letters, ∀ q, eC (τC a q) = a (eC q) :=
    fun a ha q => hiCr _ (hclosed a ha _ (heCR q))
  -- the quotient on `Rᶜ ∪ {0}`
  have h0c : (0 : Fin n) ∈ insert 0 Rᶜ := Finset.mem_insert_self _ _
  have hXc : (insert 0 Rᶜ).card = c + 1 := by
    rw [Finset.card_insert_of_notMem (by simpa using hz), Finset.card_compl, Fintype.card_fin]
  obtain ⟨eB, heBi, heB0, heBr⟩ := emb_of_finset (insert 0 Rᶜ) h0c c hXc
  set iB := Function.invFun eB with hiB
  have hiBl : ∀ i, iB (eB i) = i := Function.leftInverse_invFun heBi
  have hiBr : ∀ x ∉ R, eB (iB x) = x := fun x hx =>
    Function.invFun_eq ((heBr x).1 (Finset.mem_insert_of_mem (Finset.mem_compl.2 hx)))
  let π : Fin n → Fin (c + 1) := fun q => if q ∈ R then 0 else iB q
  have hπ0 : π 0 = 0 := by simp [π, hz]
  have hπR : ∀ x, π x = 0 → x ∈ R := by
    intro x hx
    by_contra hxR
    simp only [π, if_neg hxR] at hx
    have := hiBr x hxR
    rw [hx, heB0] at this
    exact hxR (this ▸ hz)
  let τB : Letter n → Letter (c + 1) := fun a i => π (a (eB i))
  let B : Automaton (c + 1) :=
    { letters := τB '' A.letters
      sink_fixed := by
        rintro _ ⟨a, ha, rfl⟩
        change π (a (eB 0)) = 0
        rw [heB0, A.sink_fixed a ha, hπ0] }
  have hBl : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τB a = b := fun b => Iff.rfl
  have hBc : ∀ a ∈ A.letters, ∀ q, π (a q) = τB a (π q) := by
    intro a ha q
    change π (a q) = π (a (eB (π q)))
    by_cases hq : q ∈ R
    · have h1 : π q = 0 := by simp [π, hq]
      rw [h1, heB0, A.sink_fixed a ha, hπ0]
      simp [π, hclosed a ha q hq]
    · have h1 : π q = iB q := by simp [π, hq]
      rw [h1, hiBr q hq]
  refine ⟨B, C, ?_, ?_, ?_⟩
  · have := wins_push A B τB hBl π hπ0 hBc hA
    have hsurj : (Finset.univ : Finset (Fin n)).image π = Finset.univ := by
      refine Finset.eq_univ_of_forall fun i => Finset.mem_image.2 ⟨eB i, Finset.mem_univ _, ?_⟩
      by_cases hi : eB i ∈ R
      · have hmem := (heBr (eB i)).2 ⟨i, rfl⟩
        rcases Finset.mem_insert.1 hmem with h | h
        · have : i = 0 := heBi (h.trans heB0.symm)
          rw [this, heB0, hπ0]
        · exact absurd hi (Finset.mem_compl.1 h)
      · simp [π, hi, hiBl]
    rw [hsurj] at this
    exact this
  · refine wins_pull A C τC hCl eC ?_ hCc Finset.univ (wins_mono A hA (Finset.subset_univ _))
    intro q
    exact ⟨fun h => heCi (h.trans heC0.symm), fun h => h ▸ heC0⟩
  · rintro u v ⟨hu, hu0⟩ ⟨hv, hv0⟩
    obtain ⟨u', hu', rfl, hlu⟩ := lift_word A B τB hBl u hu
    obtain ⟨v', hv', rfl, hlv⟩ := lift_word A C τC hCl v hv
    refine ⟨u' ++ v', ⟨(word_append A u' v').2 ⟨hu', hv'⟩, fun q => ?_⟩, ?_⟩
    swap
    · rw [List.length_append, List.length_map, List.length_map]
    rw [act_append]
    have h1 : π (act u' q) = 0 := by rw [push_act A τB π hBc u' hu' q]; exact hu0 _
    obtain ⟨j, hj⟩ := (heCr _).1 (hπR _ h1)
    rw [← hj, ← pull_act A τC eC hCc v' hv' j, hv0, heC0]
end SinkReset.Plan
