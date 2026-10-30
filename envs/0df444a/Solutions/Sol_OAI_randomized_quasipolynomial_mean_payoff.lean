-- Prove2me | solution 1 for OAI.randomized_quasipolynomial_mean_payoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T01:11:45.603925+00:00
-- url     : https://prove2.me/submissions/190a52cc-4b30-4433-9643-9042aab4f299

import Mathlib
import Definitions.Def_RandomizedMeanPayoff
import Definitions.Def_OAIQ117R002
import Theorems.Thm_OAI_MeanPayoff_Realizer_tree_law

section
-- module Solutions.OAIQ117_RM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

section Projections
variable {V : Type} {F : Vec V → Vec V}

theorem subsolution_raise_floor (laws : OperatorLaws F) {a b a' y : Vec V}
    (hy : Subsolution F a b y) (haa' : a ≤ a') (ha'b : a' ≤ b) :
    Subsolution F a' b (fun i => max (y i) (a' i)) ∧
    subSupport a' (fun i => max (y i) (a' i)) ⊆ subSupport a y := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i; exact le_max_right _ _
  · intro i; exact max_le (hy.1.2 i) (ha'b i)
  · intro i hi
    have hiy : a' i < y i := by simpa using hi
    have heq : max (y i) (a' i) = y i := max_eq_left (le_of_lt hiy)
    dsimp only
    rw [heq]
    exact le_trans (hy.2 i (lt_of_le_of_lt (haa' i) hiy))
      (laws.mono (fun j => le_max_left (y j) (a' j)) i)
  · intro i hi
    have hiy : a' i < y i := by simpa [subSupport] using hi
    exact lt_of_le_of_lt (haa' i) hiy

theorem supersolution_lower_ceiling (laws : OperatorLaws F) {a b b' z : Vec V}
    (hz : Supersolution F a b z) (hab' : a ≤ b') (hb'b : b' ≤ b) :
    Supersolution F a b' (fun i => min (z i) (b' i)) ∧
    superSupport b' (fun i => min (z i) (b' i)) ⊆ superSupport b z := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i; exact le_min (hz.1.1 i) (hab' i)
  · intro i; exact min_le_right _ _
  · intro i hi
    have hiz : z i < b' i := by simpa using hi
    have heq : min (z i) (b' i) = z i := min_eq_left (le_of_lt hiz)
    dsimp only
    rw [heq]
    exact le_trans (laws.mono (fun j => min_le_left (z j) (b' j)) i)
      (hz.2 i (lt_of_lt_of_le hiz (hb'b i)))
  · intro i hi
    have hiz : z i < b' i := by simpa [superSupport] using hi
    exact lt_of_lt_of_le hiz (hb'b i)

theorem centerSub_support (y q : Vec V) (d A : ℤ) :
    subSupport (fun i => q i - A) (centerSub y q d A) =
      {i | d - 2 * A < y i - q i} := by
  ext i
  simp only [subSupport, centerSub, Set.mem_ofPred_eq, lt_max_iff, lt_self_iff_false,
    or_false]
  omega

theorem centerSuper_support (z q : Vec V) (e A : ℤ) :
    superSupport (fun i => q i + A) (centerSuper z q e A) =
      {i | e - 2 * A < q i - z i} := by
  ext i
  simp only [superSupport, centerSuper, Set.mem_ofPred_eq, min_lt_iff,
    lt_self_iff_false, or_false]
  omega

theorem centered_subsolution (laws : OperatorLaws F) {a b y q : Vec V} {d A : ℤ}
    (hy : Subsolution F a b y) (hq : InBox a b q)
    (hA : 0 < A) (hdev : ∀ i, y i - q i ≤ d) (hd : 2 * A ≤ d) :
    Subsolution F (fun i => q i - A) (fun i => q i + A) (centerSub y q d A) ∧
    subSupport (fun i => q i - A) (centerSub y q d A) ⊆ subSupport a y := by
  have hs : subSupport (fun i => q i - A) (centerSub y q d A) ⊆
      subSupport a y := by
    rw [centerSub_support]
    intro i hi
    have hqi : a i ≤ q i := hq.1 i
    change a i < y i
    change d - 2 * A < y i - q i at hi
    omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hs⟩
  · intro i; exact le_max_right _ _
  · intro i
    change max (y i - d + A) (q i - A) ≤ q i + A
    apply max_le
    · have := hdev i; omega
    · omega
  · intro i hi
    have hiy : y i ≤ F y i := hy.2 i (hs hi)
    have hlarge : q i - A < y i - d + A := by
      simpa only [centerSub, lt_max_iff, lt_self_iff_false, or_false] using hi
    have heq : centerSub y q d A i = y i - d + A :=
      max_eq_left (le_of_lt hlarge)
    rw [heq]
    have hmono : F (shift y (-d + A)) i ≤ F (centerSub y q d A) i := by
      apply laws.mono
      intro j
      have := le_max_left (y j - d + A) (q j - A)
      simp [shift, centerSub, sub_eq_add_neg, add_assoc]
    rw [laws.translation] at hmono
    simp only [shift] at hmono
    omega

theorem centered_supersolution (laws : OperatorLaws F) {a b z q : Vec V} {e A : ℤ}
    (hz : Supersolution F a b z) (hq : InBox a b q)
    (hA : 0 < A) (hdev : ∀ i, q i - z i ≤ e) (he : 2 * A ≤ e) :
    Supersolution F (fun i => q i - A) (fun i => q i + A) (centerSuper z q e A) ∧
    superSupport (fun i => q i + A) (centerSuper z q e A) ⊆ superSupport b z := by
  have hs : superSupport (fun i => q i + A) (centerSuper z q e A) ⊆
      superSupport b z := by
    rw [centerSuper_support]
    intro i hi
    have hqi : q i ≤ b i := hq.2 i
    change z i < b i
    change e - 2 * A < q i - z i at hi
    omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hs⟩
  · intro i
    change q i - A ≤ min (z i + e - A) (q i + A)
    apply le_min
    · have := hdev i; omega
    · omega
  · intro i; exact min_le_right _ _
  · intro i hi
    have hiz : F z i ≤ z i := hz.2 i (hs hi)
    have hsmall : z i + e - A < q i + A := by
      simpa only [centerSuper, min_lt_iff, lt_self_iff_false, or_false] using hi
    have heq : centerSuper z q e A i = z i + e - A :=
      min_eq_left (le_of_lt hsmall)
    rw [heq]
    have hmono : F (centerSuper z q e A) i ≤ F (shift z (e - A)) i := by
      apply laws.mono
      intro j
      have := min_le_left (z j + e - A) (q j + A)
      simp [shift, centerSuper, sub_eq_add_neg, add_assoc]
    rw [laws.translation] at hmono
    simp only [shift] at hmono
    omega

end Projections

theorem high_deviation_step {V : Type} {a b y q r₁ r₂ : Vec V} {d D : ℤ}
    (hyb : y ≤ b) (hD : 0 < D) (hd : 2 * D ≤ d)
    (hdev : ∀ i, y i - q i ≤ d)
    (hr₁ : ∀ i, q i - D ≤ r₁ i)
    (hr₂ : centerSub y q d D ≤ r₂) :
    ∀ i, y i - averageStep a b r₁ r₂ i ≤ d := by
  intro i
  have hq := hdev i
  have h1 := hr₁ i
  have h2 := le_trans (le_max_left (y i - d + D) (q i - D)) (hr₂ i)
  have hb : y i ≤ b i := hyb i
  have havg : y i - d ≤ (r₁ i + r₂ i) / 2 := by omega
  have hclip : y i - d ≤ min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) :=
    le_min (by omega) (le_trans havg (le_max_right _ _))
  change y i - min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ d
  omega

theorem high_bad_step {V : Type} {a b y q r₁ r₂ : Vec V} {d D : ℤ}
    (hyb : y ≤ b) (hD : 0 < D) (hd : 2 * D ≤ d)
    (hr₁ : centerSub y q d D ≤ r₁) (hr₂ : centerSub y q d D ≤ r₂) :
    ∀ i, y i - averageStep a b r₁ r₂ i ≤ d - D := by
  intro i
  have h1 := le_trans (le_max_left (y i - d + D) (q i - D)) (hr₁ i)
  have h2 := le_trans (le_max_left (y i - d + D) (q i - D)) (hr₂ i)
  have hb : y i ≤ b i := hyb i
  have havg : y i - d + D ≤ (r₁ i + r₂ i) / 2 := by omega
  have hclip : y i - d + D ≤ min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) :=
    le_min (by omega) (le_trans havg (le_max_right _ _))
  change y i - min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ d - D
  omega

theorem low_deviation_step {V : Type} {a b z q r₁ r₂ : Vec V} {e D : ℤ}
    (haz : a ≤ z) (hD : 0 < D) (he : 2 * D ≤ e)
    (hdev : ∀ i, q i - z i ≤ e)
    (hr₁ : r₁ ≤ centerSuper z q e D)
    (hr₂ : ∀ i, r₂ i ≤ q i + D) :
    ∀ i, averageStep a b r₁ r₂ i - z i ≤ e := by
  intro i
  have hq := hdev i
  have h1 : r₁ i ≤ z i + e - D := le_trans (hr₁ i) (min_le_left (z i + e - D) (q i + D))
  have h2 := hr₂ i
  have ha : a i ≤ z i := haz i
  have havg : (r₁ i + r₂ i) / 2 ≤ z i + e := by omega
  have hclip : min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ z i + e :=
    le_trans (min_le_right _ _) (max_le (by omega) havg)
  change min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) - z i ≤ e
  omega

theorem low_bad_step {V : Type} {a b z q r₁ r₂ : Vec V} {e D : ℤ}
    (haz : a ≤ z) (hD : 0 < D) (he : 2 * D ≤ e)
    (hr₁ : r₁ ≤ centerSuper z q e D) (hr₂ : r₂ ≤ centerSuper z q e D) :
    ∀ i, averageStep a b r₁ r₂ i - z i ≤ e - D := by
  intro i
  have h1 : r₁ i ≤ z i + e - D := le_trans (hr₁ i) (min_le_left (z i + e - D) (q i + D))
  have h2 : r₂ i ≤ z i + e - D := le_trans (hr₂ i) (min_le_left (z i + e - D) (q i + D))
  have ha : a i ≤ z i := haz i
  have havg : (r₁ i + r₂ i) / 2 ≤ z i + e - D := by omega
  have hclip : min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ z i + e - D :=
    le_trans (min_le_right _ _) (max_le (by omega) havg)
  change min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) - z i ≤ e - D
  omega

theorem no_tight_sequence (G : Game) (p : Vec (Fin G.n))
    (v : ℕ → Fin G.n) (w : ℕ → ℤ)
    (h : ∀ k, p (v k) = (G.n + 1 : ℤ) * w k + 1 + p (v (k + 1))) : False := by
  have hmod : ∀ k : ℕ,
      p (v k) + (k : ℤ) ≡ p (v 0) [ZMOD (G.n + 1 : ℤ)] := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      apply Int.ModEq.trans _ ih
      apply Int.modEq_iff_dvd.mpr
      use w k
      have hk := h k
      push_cast
      linarith
  have hinj : Function.Injective (fun k : Fin (G.n + 1) => v k.val) := by
    intro i j hij
    change v i.val = v j.val at hij
    apply Fin.ext
    have hm := (hmod i.val).trans (hmod j.val).symm
    rw [hij] at hm
    have hc := Int.ModEq.add_left_cancel' (p (v j.val)) hm
    have hn : i.val ≡ j.val [MOD (G.n + 1)] :=
      Int.natCast_modEq_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hc)
    exact hn.eq_of_lt_of_lt i.isLt j.isLt
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

theorem comparison_step (G : Game) {a b y z : Vec (Fin G.n)}
    (hy : Subsolution (operator G) a b y)
    (hz : Supersolution (operator G) a b z)
    {d : ℤ} (hd : 0 < d) (hdev : ∀ j, y j - z j ≤ d)
    (i : Fin G.n) (hi : y i - z i = d) :
    ∃ e : Fin G.m, G.tail e = i ∧
      y (G.head e) - z (G.head e) = d ∧
      y i = transformed G e + y (G.head e) := by
  have hay : a i < y i := by have hzi : a i ≤ z i := hz.1.1 i; omega
  have hzb : z i < b i := by have hyi : y i ≤ b i := hy.1.2 i; omega
  have hys := hy.2 i hay
  have hzs := hz.2 i hzb
  have hmono : operator G y i ≤ operator G z i + d := by
    have hm := (operator_laws G).mono (a := y) (b := shift z d)
      (fun j => by have := hdev j; dsimp [shift]; omega) i
    rw [(operator_laws G).translation] at hm
    exact hm
  have hyeq : y i = operator G y i := by omega
  have hzeq : z i = operator G z i := by omega
  by_cases ho : G.maxOwner i = true
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup' (outgoing_nonempty G i)
      (fun e => transformed G e + y (G.head e))
    have htail : G.tail e = i := (Finset.mem_filter.mp he).2
    have hye : y i = transformed G e + y (G.head e) := by
      rw [hyeq, operator, ite_eq_left ho]; exact heq
    have hzle : transformed G e + z (G.head e) ≤ z i := by
      rw [hzeq, operator, ite_eq_left ho]
      exact Finset.le_sup' (fun e => transformed G e + z (G.head e)) he
    exact ⟨e, htail, by have := hdev (G.head e); omega, hye⟩
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
      (fun e => transformed G e + z (G.head e))
    have htail : G.tail e = i := (Finset.mem_filter.mp he).2
    have hze : z i = transformed G e + z (G.head e) := by
      rw [hzeq, operator, ite_eq_right ho]; exact heq
    have hyle : y i ≤ transformed G e + y (G.head e) := by
      rw [hyeq, operator, ite_eq_right ho]
      exact Finset.inf'_le (fun e => transformed G e + y (G.head e)) he
    have hj := hdev (G.head e)
    exact ⟨e, htail, by omega, by omega⟩

theorem box_comparison (G : Game) {a b y z : Vec (Fin G.n)}
    (hy : Subsolution (operator G) a b y)
    (hz : Supersolution (operator G) a b z) : y ≤ z := by
  classical
  let : Nonempty (Fin G.n) := ⟨⟨0, G.positive⟩⟩
  let d : ℤ := Finset.univ.sup' Finset.univ_nonempty (fun i => y i - z i)
  have hdev : ∀ i, y i - z i ≤ d := fun i =>
    Finset.le_sup' (fun j => y j - z j) (Finset.mem_univ i)
  by_contra h
  change ¬ (∀ i, y i ≤ z i) at h
  obtain ⟨k, hk⟩ := not_forall.mp h
  have hd : 0 < d := by have := hdev k; omega
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin G.n))
    (fun i => y i - z i)
  let S := {i : Fin G.n // y i - z i = d}
  let s₀ : S := ⟨v, hv.symm⟩
  have hs : ∀ s : S, ∃ e : Fin G.m, G.tail e = s.val ∧
      y (G.head e) - z (G.head e) = d ∧
      y s.val = transformed G e + y (G.head e) :=
    fun s => comparison_step G hy hz hd hdev s.val s.property
  choose edge hedge using hs
  let next : S → S := fun s => ⟨G.head (edge s), (hedge s).2.1⟩
  let path : ℕ → S := fun k => next^[k] s₀
  apply no_tight_sequence G y (fun k => (path k).val)
    (fun k => G.weight (edge (path k)))
  intro k
  have heq := (hedge (path k)).2.2
  simpa only [path, Function.iterate_succ_apply', next, transformed] using heq

theorem no_tight_segment (G : Game) (p : Vec (Fin G.n))
    (v : ℕ → Fin G.n) (w : ℕ → ℤ)
    (h : ∀ k < G.n, p (v k) = (G.n + 1 : ℤ) * w k + 1 + p (v (k + 1))) : False := by
  have hmod : ∀ k : ℕ, k ≤ G.n →
      p (v k) + (k : ℤ) ≡ p (v 0) [ZMOD (G.n + 1 : ℤ)] := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      apply Int.ModEq.trans _ (ih (by omega))
      apply Int.modEq_iff_dvd.mpr
      use w k
      have hstep := h k (by omega)
      push_cast
      linarith
  have hinj : Function.Injective (fun k : Fin (G.n + 1) => v k.val) := by
    intro i j hij
    change v i.val = v j.val at hij
    apply Fin.ext
    have hm := (hmod i.val (by omega)).trans (hmod j.val (by omega)).symm
    rw [hij] at hm
    have hc := Int.ModEq.add_left_cancel' (p (v j.val)) hm
    have hn : i.val ≡ j.val [MOD (G.n + 1)] :=
      Int.natCast_modEq_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hc)
    exact hn.eq_of_lt_of_lt i.isLt j.isLt
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

theorem operator_attained (G : Game) (p : Vec (Fin G.n)) (i : Fin G.n) :
    ∃ e : Fin G.m, G.tail e = i ∧ operator G p i = transformed G e + p (G.head e) := by
  by_cases ho : G.maxOwner i = true
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup' (outgoing_nonempty G i)
      (fun e => transformed G e + p (G.head e))
    exact ⟨e, (Finset.mem_filter.mp he).2, by simpa [operator, ho] using heq⟩
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
      (fun e => transformed G e + p (G.head e))
    exact ⟨e, (Finset.mem_filter.mp he).2, by simpa [operator, ho] using heq⟩

theorem solution_near_boundary (G : Game) {x : Vec (Fin G.n)} {B W : ℤ}
    (hW : 0 ≤ W) (hweights : ∀ e, |transformed G e| ≤ W)
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => B) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => B) x) :
    ∀ i, x i ≤ G.n * W ∨ B - G.n * W ≤ x i := by
  classical
  choose edge hedge using operator_attained G x
  let next : Fin G.n → Fin G.n := fun i =>
    if 0 < x i ∧ x i < B then G.head (edge i) else i
  have hstep : ∀ i, |x (next i) - x i| ≤ W := by
    intro i
    by_cases hi : 0 < x i ∧ x i < B
    · have hsub := hx.1.2 i hi.1
      have hsuper := hx.2.2 i hi.2
      have he := (hedge i).2
      have hw := hweights (edge i)
      simp only [next, ite_eq_left hi]
      rw [show x (G.head (edge i)) - x i = -transformed G (edge i) by omega,
        abs_neg]
      exact hw
    · simp only [next, ite_eq_right hi, sub_self, abs_zero]; exact hW
  intro start
  let path : ℕ → Fin G.n := fun k => next^[k] start
  have hmove : ∀ k, |x (path k) - x start| ≤ k * W := by
    intro k
    induction k with
    | zero => simp [path]
    | succ k ih =>
      have hs := hstep (path k)
      have hp : path (k + 1) = next (path k) := Function.iterate_succ_apply' next k start
      rw [← hp] at hs
      calc
        |x (path (k + 1)) - x start| =
          |(x (path (k + 1)) - x (path k)) + (x (path k) - x start)| := by congr 1; ring
        _ ≤ |x (path (k + 1)) - x (path k)| + |x (path k) - x start| := abs_add_le _ _
        _ ≤ W + k * W := add_le_add hs ih
        _ = (↑(k + 1) : ℤ) * W := by push_cast; ring
  have hboundary : ∃ k < G.n, ¬ (0 < x (path k) ∧ x (path k) < B) := by
    by_contra h
    push Not at h
    apply no_tight_segment G x path (fun k => G.weight (edge (path k)))
    intro k hk
    have hi := h k hk
    have hsub := hx.1.2 (path k) hi.1
    have hsuper := hx.2.2 (path k) hi.2
    have hp : path (k + 1) = G.head (edge (path k)) := by
      change next^[k + 1] start = _
      rw [Function.iterate_succ_apply']
      exact ite_eq_left hi
    rw [hp]
    have he := (hedge (path k)).2
    change x (path k) = transformed G (edge (path k)) + x (G.head (edge (path k)))
    omega
  obtain ⟨k, hk, hbound⟩ := hboundary
  have hlo : 0 ≤ x (path k) := hx.1.1.1 (path k)
  have hhi : x (path k) ≤ B := hx.1.1.2 (path k)
  have hm := hmove k
  have hk' : (k : ℤ) ≤ G.n := by omega
  have hkn := mul_le_mul_of_nonneg_right hk' hW
  have ha := (abs_le.mp hm)
  by_cases he : x (path k) = 0
  · left; omega
  · right; have he' : x (path k) = B := by omega
    omega

theorem exists_rounding_shift {n : ℕ} (p : Vec (Fin n)) :
    ∃ c : ℤ, ∀ i, (p i - c) % (n + 1 : ℤ) ≠ 0 := by
  classical
  have hN : (0 : ℤ) < n + 1 := by omega
  let residue : Fin n → Fin (n + 1) := fun i =>
    ⟨(p i % (n + 1 : ℤ)).toNat,
      (Int.toNat_lt (Int.emod_nonneg _ (ne_of_gt hN))).mpr (by
        simpa only [Nat.cast_add, Nat.cast_one] using Int.emod_lt_of_pos (p i) hN)⟩
  have hns : ¬ Function.Surjective residue := by
    intro hs
    have hc := Fintype.card_le_of_surjective residue hs
    simp only [Fintype.card_fin] at hc
    omega
  have hex : ∃ c : Fin (n + 1), ∀ i, residue i ≠ c := by
    simpa only [Function.Surjective, not_forall, not_exists] using hns
  obtain ⟨c, hc⟩ := hex
  refine ⟨c.val, ?_⟩
  intro i hi
  apply hc i
  apply Fin.ext
  change (p i % (n + 1 : ℤ)).toNat = c.val
  have hm : (c.val : ℤ) ≡ p i [ZMOD (n + 1 : ℤ)] :=
    Int.modEq_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hi)
  have hcmod : (c.val : ℤ) % (n + 1 : ℤ) = c.val :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast c.isLt)
  change (c.val : ℤ) % (n + 1 : ℤ) = p i % (n + 1 : ℤ) at hm
  rw [hcmod] at hm
  rw [← hm]
  simp

theorem rounded_high_edge {N a b w c : ℤ} (hN : 0 < N)
    (hgap : (a - c) % N ≠ 0) (h : a ≤ N * w + 1 + b) :
    (a - c) / N ≤ w + (b - c) / N := by
  have ha := Int.ediv_emod_unique (a := a - c) (b := N)
    (r := (a - c) % N) (q := (a - c) / N) hN
  have hb := Int.ediv_emod_unique (a := b - c) (b := N)
    (r := (b - c) % N) (q := (b - c) / N) hN
  have hqa := ha.mp ⟨rfl, rfl⟩
  have hqb := hb.mp ⟨rfl, rfl⟩
  by_contra hn
  have hq : w + (b - c) / N + 1 ≤ (a - c) / N := by omega
  have hp := mul_le_mul_of_nonneg_left hq (le_of_lt hN)
  have hra : 1 ≤ (a - c) % N := by omega
  have hrb : (b - c) % N ≤ N - 1 := by omega
  nlinarith [hqa.1, hqb.1]

theorem transformed_le_bound (G : Game) (e : Fin G.m) : |transformed G e| ≤ weightBound G := by
  have h := Finset.le_sup (f := fun e : Fin G.m => (transformed G e).natAbs) (Finset.mem_univ e)
  have hc : ((transformed G e).natAbs : ℤ) ≤
      ((Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hc
  exact hc.trans (le_max_right _ _)

theorem top_bands (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) :
    ∀ i, x i ≤ G.n * weightBound G ∨ 7 * G.n * weightBound G ≤ x i := by
  intro i
  have h := solution_near_boundary G (le_of_lt (weightBound_positive G))
    (transformed_le_bound G) hx i
  simpa only [topWidth, show 8 * (G.n : ℤ) * weightBound G - G.n * weightBound G =
    7 * G.n * weightBound G by ring] using h

theorem max_edge_le_operator (G : Game) (p : Vec (Fin G.n))
    {i : Fin G.n} (ho : G.maxOwner i = true) {e : Fin G.m} (he : G.tail e = i) :
    transformed G e + p (G.head e) ≤ operator G p i := by
  rw [operator, ite_eq_left ho]
  exact Finset.le_sup' (fun e => transformed G e + p (G.head e)) (by simp [outgoing, he])

theorem operator_le_min_edge (G : Game) (p : Vec (Fin G.n))
    {i : Fin G.n} (ho : G.maxOwner i ≠ true) {e : Fin G.m} (he : G.tail e = i) :
    operator G p i ≤ transformed G e + p (G.head e) := by
  rw [operator, ite_eq_right ho]
  exact Finset.inf'_le (fun e => transformed G e + p (G.head e)) (by simp [outgoing, he])

theorem move_tail (G : Game) (σ τ : Strategy G) (v : Fin G.n)
    (history : List (Fin G.m)) : G.tail (move G σ τ v history) = v := by
  unfold move
  split
  · exact (σ history v).property
  · exact (τ history v).property

theorem next_position (G : Game) (σ τ : Strategy G) (v : Fin G.n) (t : ℕ) :
    (position G σ τ v (t + 1)).1 = G.head (play G σ τ v t) := rfl

theorem high_edge_stays_high (G : Game) {x : Vec (Fin G.n)}
    (hbands : ∀ i, x i ≤ G.n * weightBound G ∨ 7 * G.n * weightBound G ≤ x i)
    {i : Fin G.n} {e : Fin G.m}
    (hi : 7 * G.n * weightBound G ≤ x i)
    (he : x i ≤ transformed G e + x (G.head e)) :
    7 * G.n * weightBound G ≤ x (G.head e) := by
  rcases hbands (G.head e) with hl | hh
  · have hw := (abs_le.mp (transformed_le_bound G e)).2
    have hn : (1 : ℤ) ≤ G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hnW : weightBound G ≤ G.n * weightBound G := by nlinarith
    nlinarith
  · exact hh

theorem low_edge_stays_low (G : Game) {x : Vec (Fin G.n)}
    (hbands : ∀ i, x i ≤ G.n * weightBound G ∨ 7 * G.n * weightBound G ≤ x i)
    {i : Fin G.n} {e : Fin G.m}
    (hi : x i ≤ G.n * weightBound G)
    (he : transformed G e + x (G.head e) ≤ x i) :
    x (G.head e) ≤ G.n * weightBound G := by
  rcases hbands (G.head e) with hl | hh
  · exact hl
  · have hw := (abs_le.mp (transformed_le_bound G e)).1
    have hn : (1 : ℤ) ≤ G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hnW : weightBound G ≤ G.n * weightBound G := by nlinarith
    nlinarith

theorem high_strategy (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) :
    ∃ σ : Strategy G, ∀ τ : Strategy G, ∀ start : Fin G.n,
      7 * G.n * weightBound G ≤ x start → ∀ t : ℕ,
      7 * G.n * weightBound G ≤ x (position G σ τ start t).1 ∧
      x (position G σ τ start t).1 ≤
        transformed G (play G σ τ start t) + x (position G σ τ start (t + 1)).1 := by
  classical
  choose edge hedge using operator_attained G x
  let σ : Strategy G := fun _ i => ⟨edge i, (hedge i).1⟩
  refine ⟨σ, ?_⟩
  intro τ start hstart
  have hlocal (i : Fin G.n) (history : List (Fin G.m))
      (hi : 7 * G.n * weightBound G ≤ x i) :
      x i ≤ transformed G (move G σ τ i history) + x (G.head (move G σ τ i history)) := by
    have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hpos : 0 < x i := by nlinarith
    have hsub := hx.1.2 i hpos
    by_cases ho : G.maxOwner i = true
    · simpa only [move, ite_eq_left ho, σ] using hsub.trans_eq (hedge i).2
    · exact hsub.trans (operator_le_min_edge G x ho (move_tail G σ τ i history))
  have hstay : ∀ t : ℕ, 7 * G.n * weightBound G ≤ x (position G σ τ start t).1 := by
    intro t
    induction t with
    | zero => exact hstart
    | succ t ih =>
      rw [next_position]
      exact high_edge_stays_high G (top_bands G hx) ih
        (hlocal (position G σ τ start t).1 (position G σ τ start t).2 ih)
  intro t
  refine ⟨hstay t, ?_⟩
  rw [next_position]
  exact hlocal (position G σ τ start t).1 (position G σ τ start t).2 (hstay t)

theorem low_strategy (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) :
    ∃ τ : Strategy G, ∀ σ : Strategy G, ∀ start : Fin G.n,
      x start ≤ G.n * weightBound G → ∀ t : ℕ,
      x (position G σ τ start t).1 ≤ G.n * weightBound G ∧
      transformed G (play G σ τ start t) + x (position G σ τ start (t + 1)).1 ≤
        x (position G σ τ start t).1 := by
  classical
  choose edge hedge using operator_attained G x
  let τ : Strategy G := fun _ i => ⟨edge i, (hedge i).1⟩
  refine ⟨τ, ?_⟩
  intro σ start hstart
  have hlocal (i : Fin G.n) (history : List (Fin G.m))
      (hi : x i ≤ G.n * weightBound G) :
      transformed G (move G σ τ i history) + x (G.head (move G σ τ i history)) ≤ x i := by
    have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hlt : x i < topWidth G := by unfold topWidth; nlinarith
    have hsuper := hx.2.2 i hlt
    by_cases ho : G.maxOwner i = true
    · exact (max_edge_le_operator G x ho (move_tail G σ τ i history)).trans hsuper
    · simpa only [move, ite_eq_right ho, τ] using (hedge i).2.symm.trans_le hsuper
  have hstay : ∀ t : ℕ, x (position G σ τ start t).1 ≤ G.n * weightBound G := by
    intro t
    induction t with
    | zero => exact hstart
    | succ t ih =>
      rw [next_position]
      exact low_edge_stays_low G (top_bands G hx) ih
        (hlocal (position G σ τ start t).1 (position G σ τ start t).2 ih)
  intro t
  refine ⟨hstay t, ?_⟩
  rw [next_position]
  exact hlocal (position G σ τ start t).1 (position G σ τ start t).2 (hstay t)

theorem le_vectorBound {n : ℕ} (p : Fin n → ℤ) (i : Fin n) :
    |p i| ≤ (vectorBound p : ℤ) := by
  have h := Finset.le_sup (f := fun i => (p i).natAbs) (Finset.mem_univ i)
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

theorem average_bounds {w : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ t, |w t| ≤ M) (T : ℕ) : -M ≤ average w T ∧ average w T ≤ M := by
  by_cases hT : T = 0
  · simp [hT, average, hM, neg_nonpos.mpr hM]
  have ht : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT
  constructor
  · apply (le_div_iff₀ ht).2
    calc
      -M * (T : ℝ) = ∑ j ∈ Finset.range T, -M := by simp; ring
      _ ≤ ∑ j ∈ Finset.range T, w j :=
        Finset.sum_le_sum (fun j _ => (abs_le.mp (hw j)).1)
  · apply (div_le_iff₀ ht).2
    calc
      (∑ j ∈ Finset.range T, w j) ≤ ∑ j ∈ Finset.range T, M :=
        Finset.sum_le_sum (fun j _ => (abs_le.mp (hw j)).2)
      _ = M * (T : ℝ) := by simp; ring

theorem payoff_bounded (G : Game) (π : ℕ → Fin G.m) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (average (fun t => (G.weight (π t) : ℝ))) ∧
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (average (fun t => (G.weight (π t) : ℝ))) := by
  let M : ℝ := vectorBound G.weight
  have hM : 0 ≤ M := by positivity
  have hw (t : ℕ) : |(G.weight (π t) : ℝ)| ≤ M := by
    dsimp [M]
    exact_mod_cast le_vectorBound G.weight (π t)
  exact ⟨Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun t => (average_bounds hM hw t).2),
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun t => (average_bounds hM hw t).1)⟩

theorem lower_average_from_potential {w p : ℕ → ℝ} {K : ℝ}
    (hp : ∀ t, |p t| ≤ K) (he : ∀ t, p t - p (t + 1) ≤ w t) (T : ℕ) :
    (-2 * K) / (T : ℝ) ≤ average w T := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
  calc
    -2 * K ≤ p 0 - p T := by
      have h0 := (abs_le.mp (hp 0)).1
      have hT := (abs_le.mp (hp T)).2
      linarith
    _ = ∑ j ∈ Finset.range T, (p j - p (j + 1)) := (Finset.sum_range_sub' p T).symm
    _ ≤ ∑ j ∈ Finset.range T, w j := Finset.sum_le_sum fun j _ => he j

theorem upper_average_from_potential {w p : ℕ → ℝ} {K N δ : ℝ}
    (hN : 0 < N) (hp : ∀ t, |p t| ≤ K)
    (he : ∀ t, N * w t + δ ≤ p t - p (t + 1))
    {T : ℕ} (hT : 0 < T) :
    average w T ≤ (2 * K / N) / (T : ℝ) - δ / N := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : N * (∑ j ∈ Finset.range T, w j) + (T : ℝ) * δ ≤ 2 * K := by
    calc
      N * (∑ j ∈ Finset.range T, w j) + (T : ℝ) * δ =
          ∑ j ∈ Finset.range T, (N * w j + δ) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range T, (p j - p (j + 1)) :=
        Finset.sum_le_sum fun j _ => he j
      _ = p 0 - p T := Finset.sum_range_sub' p T
      _ ≤ 2 * K := by
        have h0 := (abs_le.mp (hp 0)).2
        have hT := (abs_le.mp (hp T)).1
        linarith
  have hd := div_le_div_of_nonneg_right hs (le_of_lt (mul_pos hN ht))
  have hleft : (N * (∑ j ∈ Finset.range T, w j) + (T : ℝ) * δ) / (N * T) =
      average w T + δ / N := by
    unfold average
    field_simp
  have hright : 2 * K / (N * (T : ℝ)) = (2 * K / N) / T := by ring
  rw [hleft, hright] at hd
  linarith

theorem high_payoff (G : Game) {x : Vec (Fin G.n)} (σ τ : Strategy G)
    (start : Fin G.n)
    (he : ∀ t, x (position G σ τ start t).1 ≤
      transformed G (play G σ τ start t) + x (position G σ τ start (t + 1)).1) :
    0 ≤ meanPayoff G (play G σ τ start) := by
  obtain ⟨c, hc⟩ := exists_rounding_shift x
  let q (i : Fin G.n) : ℤ := (x i - c) / (G.n + 1 : ℤ)
  let p (t : ℕ) : ℝ := q (position G σ τ start t).1
  let K : ℝ := vectorBound q
  have hp (t : ℕ) : |p t| ≤ K := by
    dsimp [p, K]
    exact_mod_cast le_vectorBound q (position G σ τ start t).1
  have hedge (t : ℕ) : p t - p (t + 1) ≤ (G.weight (play G σ τ start t) : ℝ) := by
    have hN : (0 : ℤ) < G.n + 1 := by omega
    have h := rounded_high_edge hN (hc (position G σ τ start t).1) (he t)
    change q (position G σ τ start t).1 ≤
      G.weight (play G σ τ start t) + q (position G σ τ start (t + 1)).1 at h
    have hr : p t ≤ (G.weight (play G σ τ start t) : ℝ) + p (t + 1) := by
      dsimp [p]
      exact_mod_cast h
    linarith
  have hl := lower_average_from_potential hp hedge
  have ht := tendsto_const_div_atTop_nhds_zero_nat (-2 * K)
  have hb := (payoff_bounded G (play G σ τ start)).1
  have hcb : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (average (fun t => (G.weight (play G σ τ start t) : ℝ))) :=
    Filter.IsBounded.isCobounded_flip hb
  have hm := Filter.liminf_le_liminf (Filter.Eventually.of_forall hl)
    ht.isBoundedUnder_ge hcb
  rw [ht.liminf_eq] at hm
  exact hm

theorem low_payoff (G : Game) {x : Vec (Fin G.n)} (σ τ : Strategy G)
    (start : Fin G.n)
    (he : ∀ t, transformed G (play G σ τ start t) +
      x (position G σ τ start (t + 1)).1 ≤ x (position G σ τ start t).1) :
    meanPayoff G (play G σ τ start) ≤ -1 / (G.n + 1 : ℝ) := by
  let p (t : ℕ) : ℝ := x (position G σ τ start t).1
  let K : ℝ := vectorBound x
  have hp (t : ℕ) : |p t| ≤ K := by
    dsimp [p, K]
    exact_mod_cast le_vectorBound x (position G σ τ start t).1
  have hedge (t : ℕ) : (G.n + 1 : ℝ) * G.weight (play G σ τ start t) + 1 ≤
      p t - p (t + 1) := by
    have h := he t
    unfold transformed at h
    have hr : (G.n + 1 : ℝ) * G.weight (play G σ τ start t) + 1 + p (t + 1) ≤ p t := by
      dsimp [p]
      exact_mod_cast h
    linarith
  have hN : (0 : ℝ) < G.n + 1 := by positivity
  have hev : ∀ᶠ T : ℕ in Filter.atTop,
      average (fun t => (G.weight (play G σ τ start t) : ℝ)) T ≤
        (2 * K / (G.n + 1 : ℝ)) / T - 1 / (G.n + 1 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    exact upper_average_from_potential hN hp hedge hT
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (2 * K / (G.n + 1 : ℝ))).sub_const
    (1 / (G.n + 1 : ℝ))
  have hcb : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun T : ℕ => (2 * K / (G.n + 1 : ℝ)) / T - 1 / (G.n + 1 : ℝ)) :=
    Filter.IsBounded.isCobounded_flip ht.isBoundedUnder_le
  have hm := Filter.liminf_le_liminf hev (payoff_bounded G (play G σ τ start)).2 hcb
  rw [ht.liminf_eq] at hm
  change meanPayoff G (play G σ τ start) ≤ (0 : ℝ) - 1 / (G.n + 1 : ℝ) at hm
  rw [show (-1 : ℝ) / (G.n + 1 : ℝ) = 0 - 1 / (G.n + 1 : ℝ) by ring]
  exact hm

theorem winning_iff_high (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) (v : Fin G.n) :
    Winning G v ↔ topWidth G / 2 < x v := by
  have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
  have hW := weightBound_positive G
  have hhalf : topWidth G / 2 = 4 * G.n * weightBound G := by
    unfold topWidth
    rw [show 8 * (G.n : ℤ) * weightBound G = (4 * G.n * weightBound G) * 2 by ring]
    omega
  constructor
  · rintro ⟨σ, hσ⟩
    rcases top_bands G hx v with hl | hh
    · obtain ⟨τ, hτ⟩ := low_strategy G hx
      have he := fun t => (hτ σ v hl t).2
      have hp := low_payoff G σ τ v he
      have hneg : (-1 : ℝ) / (G.n + 1 : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
      exact False.elim (not_lt_of_ge ((hσ τ).trans hp) hneg)
    · rw [hhalf]
      nlinarith
  · intro hv
    obtain ⟨σ, hσ⟩ := high_strategy G hx
    refine ⟨σ, fun τ => ?_⟩
    have hh : 7 * G.n * weightBound G ≤ x v := by
      rcases top_bands G hx v with hl | hh
      · rw [hhalf] at hv
        nlinarith
      · exact hh
    exact high_payoff G σ τ v fun t => (hσ τ v hh t).2

theorem mass_mono {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 ≤ a i)
    {S T : Finset (Fin n)} (hST : S ⊆ T) : mass a S ≤ mass a T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => ha i)

theorem weight_le_mass {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 ≤ a i)
    {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) : a i ≤ mass a S :=
  Finset.single_le_sum (fun i _ => ha i) hi

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Budgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

theorem small_rank_comparisons {n : ℕ} (P : Budgets n) (hR : P.parameter < 1)
    {F : Vec (Fin n) → Vec (Fin n)} {a b y z : Vec (Fin n)}
    (hy : AdmissibleSub F a b y P) (hz : AdmissibleSuper F a b z P) :
    y ≤ smallRankAnswer a b P ∧ smallRankAnswer a b P ≤ z := by
  have hprod (i : Fin n) : P.k * P.m < P.alpha i * P.beta i := by
    have hs := weight_le_mass (fun j => le_of_lt (P.density_pos j)) (Finset.mem_univ i)
    have hm := mul_le_mul_of_nonneg_left hs (le_of_lt (mul_pos P.k_pos P.m_pos))
    have hq : P.k * P.m / (P.alpha i * P.beta i) < 1 := by
      have : P.k * P.m * P.density i < 1 := hm.trans_lt hR
      simpa only [Budgets.density, mul_one_div] using this
    exact (div_lt_one (mul_pos (P.alpha_pos i) (P.beta_pos i))).mp hq
  have hya (i : Fin n) (hi : P.k < P.alpha i) : y i = a i := by
    have hlow : a i ≤ y i := hy.1.1.1 i
    by_contra hh
    have hm := weight_le_mass (fun j => le_of_lt (P.alpha_pos j))
      (show i ∈ lowerActive a y by simp [lowerActive]; omega)
    exact (not_lt_of_ge (hm.trans hy.2)) hi
  have hzb (i : Fin n) (hi : P.m < P.beta i) : z i = b i := by
    have hup : z i ≤ b i := hz.1.1.2 i
    by_contra hh
    have hm := weight_le_mass (fun j => le_of_lt (P.beta_pos j))
      (show i ∈ upperActive b z by simp [upperActive]; omega)
    exact (not_lt_of_ge (hm.trans hz.2)) hi
  constructor
  · intro i
    dsimp [smallRankAnswer]
    split_ifs with hi
    · exact hy.1.1.2 i
    · have hk : P.k < P.alpha i := by
        have hb : P.beta i ≤ P.m := le_of_not_gt hi
        have hp := hprod i
        nlinarith [P.alpha_pos i, P.k_pos, P.beta_pos i]
      rw [hya i hk]
  · intro i
    dsimp [smallRankAnswer]
    split_ifs with hi
    · exact (hzb i hi).symm.le
    · exact hz.1.1.1 i

theorem mass_halve {n : ℕ} (a : Fin n → ℚ) (H S : Finset (Fin n)) :
    mass (halve a H) S = mass a S - mass a (S ∩ H) / 2 := by
  have he (i : Fin n) : halve a H i = a i - (if i ∈ H then a i else 0) / 2 := by
    unfold halve
    split_ifs <;> ring
  simp only [mass, he, Finset.sum_sub_distrib, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_filter]
  congr 2

theorem reweight_admissible_sub {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b y : Vec (Fin n)} {H : Finset (Fin n)}
    (hy : AdmissibleSub F a b y P)
    (hw : (4 / 5) * P.k < mass P.alpha (lowerActive a y ∩ H)) :
    AdmissibleSub F a b y (P.reweightK H) := by
  refine ⟨hy.1, ?_⟩
  change mass (halve P.alpha H) (lowerActive a y) ≤ (3 / 5) * P.k
  rw [mass_halve]
  linarith [hy.2]

theorem reweight_admissible_super {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b z : Vec (Fin n)} {H : Finset (Fin n)}
    (hz : AdmissibleSuper F a b z P)
    (hw : (4 / 5) * P.m < mass P.beta (upperActive b z ∩ H)) :
    AdmissibleSuper F a b z (P.reweightM H) := by
  refine ⟨hz.1, ?_⟩
  change mass (halve P.beta H) (upperActive b z) ≤ (3 / 5) * P.m
  rw [mass_halve]
  linarith [hz.2]

namespace RandomTree

theorem expect_add {α : Type} (t : RandomTree α) (f g : α → ℚ) :
    expect t (fun a => f a + g a) = expect t f + expect t g := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [hl, hr]; ring

theorem expect_mul {α : Type} (t : RandomTree α) (c : ℚ) (f : α → ℚ) :
    expect t (fun a => c * f a) = c * expect t f := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [hl, hr]; ring

theorem expect_mono_all {α : Type} (t : RandomTree α) (f g : α → ℚ)
    (h : t.All (fun a => f a ≤ g a)) : expect t f ≤ expect t g := by
  induction t with
  | leaf a => exact h
  | coin l r hl hr =>
    have := hl h.1
    have := hr h.2
    simp only [expect_coin]
    linarith

theorem all_of_forall {α : Type} (t : RandomTree α) {P : α → Prop} (h : ∀ a, P a) :
    t.All P := by
  induction t with
  | leaf a => exact h a
  | coin l r hl hr => exact ⟨hl, hr⟩

theorem expect_mono {α : Type} (t : RandomTree α) (f g : α → ℚ)
    (h : ∀ a, f a ≤ g a) : expect t f ≤ expect t g :=
  expect_mono_all t f g (all_of_forall t h)

theorem expect_nonneg {α : Type} (t : RandomTree α) (f : α → ℚ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ expect t f := by
  simpa using expect_mono t (fun _ => 0) f h

theorem all_mono {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (h : t.All P) (hPQ : ∀ a, P a → Q a) : t.All Q := by
  induction t with
  | leaf a => exact hPQ a h
  | coin l r hl hr => exact ⟨hl h.1, hr h.2⟩

theorem probability_nonneg {α : Type} (t : RandomTree α) (P : α → Prop) :
    0 ≤ t.probability P := by
  classical
  exact expect_nonneg t _ (fun a => by split_ifs <;> norm_num)

theorem probability_le_one {α : Type} (t : RandomTree α) (P : α → Prop) :
    t.probability P ≤ 1 := by
  classical
  have := expect_mono t (fun a => if P a then 1 else 0) (fun _ => 1)
    (fun a => by split_ifs <;> norm_num)
  simpa [probability] using this

theorem probability_mono {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (h : ∀ a, P a → Q a) : t.probability P ≤ t.probability Q := by
  classical
  apply expect_mono
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

theorem probability_compl {α : Type} (t : RandomTree α) (P : α → Prop) :
    t.probability (fun a => ¬ P a) = 1 - t.probability P := by
  classical
  have he (a : α) : (if P a then (1 : ℚ) else 0) +
      (if ¬P a then (1 : ℚ) else 0) = 1 := by split_ifs <;> simp_all
  have hh := expect_add t (fun a => if P a then 1 else 0) (fun a => if ¬P a then 1 else 0)
  simp only [he, expect_const] at hh
  unfold probability
  convert (show t.expect (fun a => if ¬P a then 1 else 0) =
    1 - t.expect (fun a => if P a then 1 else 0) by linarith) using 1 ;
    congr 1 ; funext a ; by_cases h : P a <;> simp [h]

open scoped Classical

theorem trials_length {α : Type} (t : RandomTree α) (J : ℕ) :
    (trials t J).All (fun as => as.length = J) := by
  induction J with
  | zero => rfl
  | succ j hj =>
    rw [trials, all_bind]
    apply all_of_forall
    intro a
    rw [map, all_bind]
    exact all_mono _ hj (fun as hs => by simp [All, hs])

theorem moment_cons {α : Type} (P : α → Prop) (a : α) (as : List α) :
    moment P (a :: as) = (if P a then 1 else 16) * moment P as := by
  classical
  by_cases h : P a <;> simp [moment, badCount, h, pow_add]

theorem failure_moment {α : Type} (t : RandomTree α) (P : α → Prop) :
    t.expect (fun a => if P a then 1 else 16) =
      1 + 15 * t.probability (fun a => ¬ P a) := by
  classical
  have he (a : α) : (if P a then (1 : ℚ) else 16) =
      1 + 15 * (if ¬P a then 1 else 0) := by by_cases h : P a <;> norm_num [h]
  simp only [he, expect_add, expect_mul, expect_const, probability]
  congr 2
  congr 1
  funext a
  by_cases h : P a <;> simp [h]

theorem amplification_moment {α : Type} (t : RandomTree α) (P : α → Prop)
    (h : t.probability (fun a => ¬ P a) ≤ 1 / 16) (J : ℕ) :
    (trials t J).expect (moment P) ≤ 2 ^ J := by
  classical
  induction J with
  | zero => simp [trials, moment, badCount]
  | succ j hj =>
    rw [trials, expect_bind]
    simp only [expect_map, Function.comp_def, moment_cons, expect_mul]
    have he (a : α) : (if P a then (1 : ℚ) else 16) *
        (trials t j).expect (moment P) =
        (trials t j).expect (moment P) * (if P a then 1 else 16) := mul_comm _ _
    simp only [he, expect_mul, failure_moment]
    have hn := expect_nonneg (trials t j) (moment P) (fun as => by unfold moment; positivity)
    have hf := probability_nonneg t (fun a => ¬P a)
    have hu : 1 + 15 * t.probability (fun a => ¬P a) ≤ 2 := by linarith
    calc
      (trials t j).expect (moment P) * (1 + 15 * t.probability (fun a => ¬P a))
          ≤ (trials t j).expect (moment P) * 2 := mul_le_mul_of_nonneg_left hu hn
      _ ≤ 2 ^ j * 2 := mul_le_mul_of_nonneg_right hj (by norm_num)
      _ = 2 ^ (j + 1) := (pow_succ _ _).symm

theorem amplification {α : Type} (t : RandomTree α) (P : α → Prop)
    (h : t.probability (fun a => ¬ P a) ≤ 1 / 16) (J : ℕ) :
    (trials t J).probability (fun as => J ≤ 2 * badCount P as) ≤ (1 / 2 : ℚ) ^ J := by
  classical
  have he := amplification_moment t P h J
  have hm : (4 : ℚ) ^ J * (trials t J).probability (fun as => J ≤ 2 * badCount P as)
      ≤ (trials t J).expect (moment P) := by
    unfold probability
    rw [← expect_mul]
    apply expect_mono
    intro as
    split_ifs with ha
    · rw [mul_one]
      calc
        (4 : ℚ) ^ J ≤ 4 ^ (2 * badCount P as) := pow_le_pow_right₀ (by norm_num) ha
        _ = moment P as := by unfold moment; rw [pow_mul]; norm_num
    · simp only [mul_zero]
      unfold moment
      positivity
  have hh : (trials t J).probability (fun as => J ≤ 2 * badCount P as) ≤
      (2 : ℚ) ^ J / 4 ^ J := (le_div_iff₀ (by positivity)).mpr (by linarith)
  simpa only [← div_pow, show (2 : ℚ) / 4 = 1 / 2 by norm_num] using hh

end RandomTree
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree
open scoped Classical

theorem badCount_eq_countP {α : Type} (P : α → Prop) (as : List α) :
    badCount P as = as.countP (fun a => decide (¬P a)) := by
  induction as with
  | nil => rfl
  | cons a as ha => by_cases h : P a <;> simp [badCount, h, ha, Nat.add_comm]

theorem badCount_perm {α : Type} (P : α → Prop) {as bs : List α} (h : as.Perm bs) :
    badCount P as = badCount P bs := by
  simpa only [badCount_eq_countP] using h.countP_eq (fun a => decide (¬P a))

theorem badCount_sublist {α : Type} (P : α → Prop) {as bs : List α} (h : as.Sublist bs) :
    badCount P as ≤ badCount P bs := by
  simpa only [badCount_eq_countP] using
    (h.countP_le (p := fun a => decide (¬P a)))

theorem badCount_eq_length {α : Type} (P : α → Prop) (as : List α)
    (h : ∀ a ∈ as, ¬P a) : badCount P as = as.length := by
  rw [badCount_eq_countP, List.countP_eq_length]
  simpa using h

theorem badCount_map_le {α β : Type} (f : α → β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ a, P a → Q (f a)) (as : List α) : badCount Q (as.map f) ≤ badCount P as := by
  induction as with
  | nil => rfl
  | cons a as ha =>
    by_cases hp : P a <;> by_cases hq : Q (f a) <;> simp_all [badCount] ; omega

end RandomTree

open RandomTree in
 theorem medianInt_lower_failure {as : List ℤ} {y : ℤ} (ha : 0 < as.length)
    (hf : medianInt as < y) : as.length ≤ 2 * badCount (fun a => y ≤ a) as := by
  let bs := as.mergeSort (· ≤ ·)
  have hlen : bs.length = as.length := List.length_mergeSort as
  have hk : as.length / 2 < bs.length := by rw [hlen]; exact Nat.div_lt_self ha (by norm_num)
  have hsort : bs.SortedLE := List.sortedLE_mergeSort
  have hf' : bs[as.length / 2] < y := by simpa only [medianInt, dite_eq_left ha] using hf
  have hbad : badCount (fun a => y ≤ a) (bs.take (as.length / 2 + 1)) = as.length / 2 + 1 := by
    rw [badCount_eq_length]
    · simp only [List.length_take, hlen]
      omega
    · intro a hm
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hm
      have hle : bs[j] ≤ bs[as.length / 2] :=
        hsort.getElem_le_getElem_of_le (by omega)
      omega
  have hm := badCount_sublist (fun a => y ≤ a) (List.take_sublist (as.length / 2 + 1) bs)
  rw [hbad, badCount_perm _ (List.mergeSort_perm as (· ≤ ·))] at hm
  omega

open RandomTree in
 theorem medianInt_upper_failure {as : List ℤ} {z : ℤ} (ha : 0 < as.length)
    (hf : z < medianInt as) : as.length ≤ 2 * badCount (fun a => a ≤ z) as := by
  let bs := as.mergeSort (· ≤ ·)
  have hlen : bs.length = as.length := List.length_mergeSort as
  have hk : as.length / 2 < bs.length := by rw [hlen]; exact Nat.div_lt_self ha (by norm_num)
  have hsort : bs.SortedLE := List.sortedLE_mergeSort
  have hf' : z < bs[as.length / 2] := by simpa only [medianInt, dite_eq_left ha] using hf
  have hbad : badCount (fun a => a ≤ z) (bs.drop (as.length / 2)) = as.length - as.length / 2 := by
    rw [badCount_eq_length]
    · simp only [List.length_drop, hlen]
    · intro a hm
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hm
      have hle : bs[as.length / 2] ≤ bs[as.length / 2 + j] :=
        hsort.getElem_le_getElem_of_le (by omega)
      omega
  have hm := badCount_sublist (fun a => a ≤ z) (List.drop_sublist (as.length / 2) bs)
  rw [hbad, badCount_perm _ (List.mergeSort_perm as (· ≤ ·))] at hm
  omega

open RandomTree in
 theorem median_lower_failure {V : Type} {as : List (Vec V)} {y : Vec V}
    (ha : 0 < as.length) (hf : ¬ y ≤ median as) :
    as.length ≤ 2 * badCount (fun p => y ≤ p) as := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, median as i < y i := by
    simpa only [Pi.le_def, not_forall, not_le] using hf
  have hm := medianInt_lower_failure (by simpa : 0 < (as.map (fun p => p i)).length) hi
  have hb := badCount_map_le (fun p : Vec V => p i) (fun p => y ≤ p)
    (fun a => y i ≤ a) (fun p hp => hp i) as
  simp only [List.length_map] at hm
  omega

open RandomTree in
 theorem median_upper_failure {V : Type} {as : List (Vec V)} {z : Vec V}
    (ha : 0 < as.length) (hf : ¬ median as ≤ z) :
    as.length ≤ 2 * badCount (fun p => p ≤ z) as := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i < median as i := by
    simpa only [Pi.le_def, not_forall, not_le] using hf
  have hm := medianInt_upper_failure (by simpa : 0 < (as.map (fun p => p i)).length) hi
  have hb := badCount_map_le (fun p : Vec V => p i) (fun p => p ≤ z)
    (fun a => a ≤ z i) (fun p hp => hp i) as
  simp only [List.length_map] at hm
  omega

end MeanPayoff

namespace MeanPayoff
namespace RandomTree

theorem probability_map {α β : Type} (t : RandomTree α) (f : α → β) (P : β → Prop) :
    (t.map f).probability P = t.probability (fun a => P (f a)) := by
  classical
  simp only [probability, expect_map, Function.comp_def]

theorem probability_mono_all {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (h : t.All (fun a => P a → Q a)) : t.probability P ≤ t.probability Q := by
  classical
  apply expect_mono_all
  apply all_mono _ h
  intro a ha
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

theorem probability_union {α : Type} (t : RandomTree α) (P Q : α → Prop) :
    t.probability (fun a => P a ∨ Q a) ≤ t.probability P + t.probability Q := by
  classical
  unfold probability
  rw [← expect_add]
  apply expect_mono
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> norm_num [hp, hq]

theorem trials_all {α : Type} (t : RandomTree α) {P : α → Prop}
    (h : t.All P) (J : ℕ) : (trials t J).All (fun as => ∀ a ∈ as, P a) := by
  induction J with
  | zero => simp [trials, All]
  | succ j hj =>
    rw [trials, all_bind]
    apply all_mono _ h
    intro a ha
    rw [map, all_bind]
    apply all_mono _ hj
    intro as has
    simpa [All] using (show ∀ b ∈ a :: as, P b by simp_all)

theorem all_and {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (hp : t.All P) (hq : t.All Q) : t.All (fun a => P a ∧ Q a) := by
  induction t with
  | leaf a => exact ⟨hp, hq⟩
  | coin l r hl hr => exact ⟨hl hp.1 hq.1, hr hp.2 hq.2⟩

end RandomTree


theorem globalJ_positive (n Bmax : ℕ) : 0 < globalJ n Bmax := by unfold globalJ; omega

namespace SolveBox

theorem repeated_lower {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : RandomTree (BoxVector I)) {y : Vec (Fin n)}
    (h : t.probability (fun p => ¬y ≤ p.val) ≤ 1 / 16) {J : ℕ} (hJ : 0 < J) :
    (I.repeated t J).probability (fun p => ¬y ≤ p.val) ≤ (1 / 2 : ℚ) ^ J := by
  rw [repeated, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification t (fun p => y ≤ p.val) h J)
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length t J)
  intro as has hf
  have hlen : 0 < as.length := by omega
  simp only [medianBox, dite_eq_left hlen] at hf
  have hm := median_lower_failure (by simpa using hlen : 0 < (as.map Subtype.val).length) hf
  have hc := RandomTree.badCount_map_le Subtype.val (fun p : BoxVector I => y ≤ p.val)
    (fun p => y ≤ p) (fun _ hp => hp) as
  simp only [List.length_map] at hm
  omega

theorem repeated_upper {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : RandomTree (BoxVector I)) {z : Vec (Fin n)}
    (h : t.probability (fun p => ¬p.val ≤ z) ≤ 1 / 16) {J : ℕ} (hJ : 0 < J) :
    (I.repeated t J).probability (fun p => ¬p.val ≤ z) ≤ (1 / 2 : ℚ) ^ J := by
  rw [repeated, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification t (fun p => p.val ≤ z) h J)
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length t J)
  intro as has hf
  have hlen : 0 < as.length := by omega
  simp only [medianBox, dite_eq_left hlen] at hf
  have hm := median_upper_failure (by simpa using hlen : 0 < (as.map Subtype.val).length) hf
  have hc := RandomTree.badCount_map_le Subtype.val (fun p : BoxVector I => p.val ≤ z)
    (fun p => p ≤ z) (fun _ hp => hp) as
  simp only [List.length_map] at hm
  omega

end SolveBox

namespace RandomTree

theorem uniformBelow_lt (k : ℕ) : (uniformBelow k).All (fun i => i < 2 ^ k) := by
  induction k with
  | zero => norm_num [uniformBelow, All]
  | succ k hk =>
    constructor
    · exact all_mono _ hk (fun i hi => by rw [pow_succ]; omega)
    · rw [map, all_bind]
      exact all_mono _ hk (fun i hi => by dsimp [All]; rw [pow_succ]; omega)

theorem expect_uniformBelow (k : ℕ) (f : ℕ → ℚ) :
    (uniformBelow k).expect f = (∑ i ∈ Finset.range (2 ^ k), f i) / (2 ^ k : ℚ) := by
  induction k generalizing f with
  | zero => simp [uniformBelow]
  | succ k hk =>
    simp only [uniformBelow, expect_coin, expect_map, Function.comp_def, hk]
    rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by omega]
    rw [Finset.sum_range_add]
    simp only [pow_succ]
    have hsum : (∑ i ∈ Finset.range (2 ^ k), f (i + 2 ^ k)) =
        ∑ i ∈ Finset.range (2 ^ k), f (2 ^ k + i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.add_comm]
    rw [hsum]
    ring

end RandomTree
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Deviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem le_deviation (G : Game) (y q : Vec (Fin G.n)) (i : Fin G.n) :
    y i - q i ≤ deviation G y q :=
  Finset.le_sup' (fun j => y j - q j) (Finset.mem_univ i)

theorem deviation_le (G : Game) {y q : Vec (Fin G.n)} {d : ℤ}
    (h : ∀ i, y i - q i ≤ d) : deviation G y q ≤ d :=
  Finset.sup'_le _ _ (fun i _ => h i)

theorem deviation_attained (G : Game) (y q : Vec (Fin G.n)) :
    ∃ i, deviation G y q = y i - q i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset (Fin G.n)).Nonempty from ⟨⟨0, G.positive⟩, Finset.mem_univ _⟩)
    (fun i => y i - q i)
  exact ⟨i, hi⟩

namespace SolveBox

theorem radius_bounds {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    I.width ≤ 64 * globalS Bmax * I.D ∧ globalS Bmax * I.D ≤ I.E ∧
    32 * globalS Bmax * I.D ≤ I.width ∧ 8 * I.E ≤ I.width := by
  have hs := globalS_large Bmax
  have hd := Nat.div_mul_le_self I.width (32 * globalS Bmax)
  have hdm := Nat.div_add_mod I.width (32 * globalS Bmax)
  have hdr := Nat.mod_lt I.width (show 0 < 32 * globalS Bmax by omega)
  have he := Nat.div_mul_le_self I.width 8
  have hem := Nat.div_add_mod I.width 8
  have her := Nat.mod_lt I.width (show 0 < 8 by omega)
  change I.width ≤ 64 * globalS Bmax * (I.width / (32 * globalS Bmax)) ∧
    globalS Bmax * (I.width / (32 * globalS Bmax)) ≤ I.width / 8 ∧
    32 * globalS Bmax * (I.width / (32 * globalS Bmax)) ≤ I.width ∧
    8 * (I.width / 8) ≤ I.width
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem midpoint_twice {n Bmax : ℕ} (I : SolveBox n Bmax) (i : Fin n) :
    I.b i - I.a i - 1 ≤ 2 * (I.midpoint.val i - I.a i) ∧
    2 * (I.midpoint.val i - I.a i) ≤ I.b i - I.a i := by
  change I.b i - I.a i - 1 ≤ 2 * ((I.a i + I.b i) / 2 - I.a i) ∧
    2 * ((I.a i + I.b i) / 2 - I.a i) ≤ I.b i - I.a i
  omega

theorem average_movement {n Bmax : ℕ} (I : SolveBox n Bmax) (q : BoxVector I)
    {A : ℤ} (_hA : 0 ≤ A) {r₁ r₂ : Vec (Fin n)}
    (h₁ : InBox (fun i => q.val i - A) (fun i => q.val i + A) r₁)
    (h₂ : InBox (fun i => q.val i - A) (fun i => q.val i + A) r₂) (i : Fin n) :
    |(I.averageClipped r₁ r₂).val i - q.val i| ≤ A := by
  have h1a : q.val i - A ≤ r₁ i := h₁.1 i
  have h1b : r₁ i ≤ q.val i + A := h₁.2 i
  have h2a : q.val i - A ≤ r₂ i := h₂.1 i
  have h2b : r₂ i ≤ q.val i + A := h₂.2 i
  have ha : I.a i ≤ q.val i := q.property.1 i
  have hb : q.val i ≤ I.b i := q.property.2 i
  rw [abs_le]
  change -A ≤ min (I.b i) (max (I.a i) ((r₁ i + r₂ i) / 2)) - q.val i ∧
    min (I.b i) (max (I.a i) ((r₁ i + r₂ i) / 2)) - q.val i ≤ A
  omega

end SolveBox

theorem highCore_support {n Bmax : ℕ} (I : SolveBox n Bmax) (y : Vec (Fin n)) :
    highCore I y ⊆ lowerActive I.a y := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  simp only [lowerActive, Finset.mem_filter, Finset.mem_univ, true_and]
  nlinarith

theorem lowCore_support {n Bmax : ℕ} (I : SolveBox n Bmax) (z : Vec (Fin n)) :
    lowCore I z ⊆ upperActive I.b z := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  simp only [upperActive, Finset.mem_filter, Finset.mem_univ, true_and]
  nlinarith

theorem high_initial_deficit (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : y ≤ I.b) {i : Fin G.n} (hi : i ∈ highCore I y) :
    (globalS Bmax : ℤ) * (deviation G y I.midpoint.val - (y i - I.midpoint.val i)) ≤
      I.width + globalS Bmax := by
  obtain ⟨j, hj⟩ := deviation_attained G y I.midpoint.val
  have hmt := I.midpoint_twice j
  have hmi := I.midpoint_twice i
  have hwj := I.width_bound j
  have hwi := I.width_bound i
  have hyj : y j ≤ I.b j := hy j
  have hcore := (Finset.mem_filter.mp hi).2
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hmul₁ := mul_le_mul_of_nonneg_left hmt.1 hs
  have hmul₂ := mul_le_mul_of_nonneg_left hmi.2 hs
  have hmul₃ := mul_le_mul_of_nonneg_left hwj hs
  have hmul₄ := mul_le_mul_of_nonneg_left hwi hs
  have hmul₅ := mul_le_mul_of_nonneg_left hyj hs
  rw [hj]
  nlinarith only [hcore, hs, hmul₁, hmul₂, hmul₃, hmul₄, hmul₅]

theorem low_initial_deficit (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : I.a ≤ z) {i : Fin G.n} (hi : i ∈ lowCore I z) :
    (globalS Bmax : ℤ) * (deviation G I.midpoint.val z - (I.midpoint.val i - z i)) ≤
      I.width + globalS Bmax := by
  obtain ⟨j, hj⟩ := deviation_attained G I.midpoint.val z
  have hmt := I.midpoint_twice j
  have hmi := I.midpoint_twice i
  have hwj := I.width_bound j
  have hwi := I.width_bound i
  have hzj : I.a j ≤ z j := hz j
  have hcore := (Finset.mem_filter.mp hi).2
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hmul₁ := mul_le_mul_of_nonneg_left hmt.2 hs
  have hmul₂ := mul_le_mul_of_nonneg_left hmi.1 hs
  have hmul₃ := mul_le_mul_of_nonneg_left hwj hs
  have hmul₄ := mul_le_mul_of_nonneg_left hwi hs
  have hmul₅ := mul_le_mul_of_nonneg_left hzj hs
  rw [hj]
  nlinarith only [hcore, hs, hmul₁, hmul₂, hmul₃, hmul₄, hmul₅]

theorem high_center_deviation (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) {y q : Vec (Fin G.n)}
    (hy : y ≤ I.b) (hcore : (highCore I y).Nonempty)
    (hq : ∀ i, |q i - I.midpoint.val i| ≤ (globalS Bmax : ℤ) * I.D) :
    2 * (I.E : ℤ) ≤ deviation G y q := by
  obtain ⟨i, hi⟩ := hcore
  have hic := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hm := I.midpoint_twice i
  have hyi : y i ≤ I.b i := hy i
  have hw := I.width_bound i
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hwgt : (y i - I.a i) ≤ I.width := by omega
  have h15 : 15 * (I.width : ℤ) ≤ 16 * (y i - I.a i) := by
    nlinarith only [hic, mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hwgt)]
  have hr := I.radius_bounds hB
  have hD : 32 * (globalS Bmax : ℤ) * I.D ≤ I.width := by exact_mod_cast hr.2.2.1
  have hE : 8 * (I.E : ℤ) ≤ I.width := by exact_mod_cast hr.2.2.2
  have hq' := (abs_le.mp (hq i)).2
  have hd := le_deviation G y q i
  nlinarith only [h15, hm.2, hw, hb, hD, hE, hq', hd]

theorem low_center_deviation (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) {z q : Vec (Fin G.n)}
    (hz : I.a ≤ z) (hcore : (lowCore I z).Nonempty)
    (hq : ∀ i, |q i - I.midpoint.val i| ≤ (globalS Bmax : ℤ) * I.D) :
    2 * (I.E : ℤ) ≤ deviation G q z := by
  obtain ⟨i, hi⟩ := hcore
  have hic := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hm := I.midpoint_twice i
  have hzi : I.a i ≤ z i := hz i
  have hw := I.width_bound i
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hwgt : (I.b i - z i) ≤ I.width := by omega
  have h15 : 15 * (I.width : ℤ) ≤ 16 * (I.b i - z i) := by
    nlinarith only [hic, mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hwgt)]
  have hr := I.radius_bounds hB
  have hD : 32 * (globalS Bmax : ℤ) * I.D ≤ I.width := by exact_mod_cast hr.2.2.1
  have hE : 8 * (I.E : ℤ) ≤ I.width := by exact_mod_cast hr.2.2.2
  have hq' := (abs_le.mp (hq i)).1
  have hd := le_deviation G q z i
  have hb' : (128 : ℤ) * globalS Bmax < I.width := by exact_mod_cast hB
  nlinarith only [h15, hm.1, hw, hb, hD, hE, hq', hd, hb', hs]


namespace RandomTree

theorem probability_zero_of_all {α : Type} (t : RandomTree α) {P : α → Prop}
    (h : t.All (fun a => ¬P a)) : t.probability P = 0 := by
  classical
  apply le_antisymm _ (probability_nonneg t P)
  have hh := expect_mono_all t (fun a => if P a then (1 : ℚ) else 0) (fun _ => 0)
    (all_mono _ h (fun a ha => by simp [ha]))
  simpa [probability] using hh

theorem bind_error {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (good : α → Prop) (bad : β → Prop) {ρ ε : ℚ} (hε : 0 ≤ ε)
    (ht : t.probability (fun a => ¬good a) ≤ ρ)
    (hf : ∀ a, good a → (f a).probability bad ≤ ε) :
    (t.bind f).probability bad ≤ ρ + ε := by
  classical
  have hs : (t.bind f).probability bad ≤ t.probability (fun a => ¬good a) + ε := by
    unfold probability
    rw [expect_bind]
    rw [← expect_const t ε, ← expect_add]
    apply expect_mono
    intro a
    by_cases ha : good a
    · simpa [ha, probability] using hf a ha
    · have hh := probability_le_one (f a) bad
      simp only [ha, not_false_eq_true, ite_true, if_true]
      change (f a).probability bad ≤ 1 + ε
      linarith
  linarith

theorem bind_probability_le {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (bad : β → Prop) {ε : ℚ} (hf : ∀ a, (f a).probability bad ≤ ε) :
    (t.bind f).probability bad ≤ ε := by
  classical
  unfold probability
  rw [expect_bind, ← expect_const t ε]
  exact expect_mono t _ _ hf

theorem map_error {α β : Type} (t : RandomTree α) (f : α → β)
    (good : α → Prop) (bad : β → Prop) {ε : ℚ}
    (ht : t.probability (fun a => ¬good a) ≤ ε)
    (hf : ∀ a, good a → ¬bad (f a)) : (t.map f).probability bad ≤ ε := by
  rw [probability_map]
  apply le_trans _ ht
  exact probability_mono t (fun a ha hg => hf a hg ha)

end RandomTree

theorem centered_active_high (G : Game) (y q : Vec (Fin G.n)) (A : ℕ) :
    lowerActive (fun i => q i - A) (centerSub y q (deviation G y q) A) = nearHigh G y q A := by
  ext i
  simp only [lowerActive, nearHigh, Finset.mem_filter, Finset.mem_univ, true_and,
    centerSub, lt_max_iff, lt_self_iff_false, or_false]
  omega

theorem centered_active_low (G : Game) (z q : Vec (Fin G.n)) (A : ℕ) :
    upperActive (fun i => q i + A) (centerSuper z q (deviation G q z) A) = nearLow G z q A := by
  ext i
  simp only [upperActive, nearLow, Finset.mem_filter, Finset.mem_univ, true_and,
    centerSuper, min_lt_iff, lt_self_iff_false, or_false]
  omega

theorem centered_admissible_high (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (q : BoxVector I) (A : ℕ) (hA : 0 < A) (hmax : 2 * A ≤ Bmax)
    (hd : 2 * (A : ℤ) ≤ deviation G y q.val) :
    AdmissibleSub (operator G) (SolveBox.centered q.val A hA hmax).a
      (SolveBox.centered q.val A hA hmax).b (centerSub y q.val (deviation G y q.val) A) P := by
  have hp := centered_subsolution (operator_laws G) hy.1 q.property
    (show (0 : ℤ) < A by exact_mod_cast hA) (le_deviation G y q.val) hd
  refine ⟨hp.1, ?_⟩
  apply le_trans _ hy.2
  apply mass_mono (fun i => (P.alpha_pos i).le)
  intro i hi
  have hi' : i ∈ subSupport (fun i => q.val i - A)
      (centerSub y q.val (deviation G y q.val) A) := (Finset.mem_filter.mp hi).2
  have hh := hp.2 hi'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩

theorem centered_admissible_low (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (q : BoxVector I) (A : ℕ) (hA : 0 < A) (hmax : 2 * A ≤ Bmax)
    (hd : 2 * (A : ℤ) ≤ deviation G q.val z) :
    AdmissibleSuper (operator G) (SolveBox.centered q.val A hA hmax).a
      (SolveBox.centered q.val A hA hmax).b (centerSuper z q.val (deviation G q.val z) A) P := by
  have hp := centered_supersolution (operator_laws G) hz.1 q.property
    (show (0 : ℤ) < A by exact_mod_cast hA) (le_deviation G q.val z) hd
  refine ⟨hp.1, ?_⟩
  apply le_trans _ hz.2
  apply mass_mono (fun i => (P.beta_pos i).le)
  intro i hi
  have hi' : i ∈ superSupport (fun i => q.val i + A)
      (centerSuper z q.val (deviation G q.val z) A) := (Finset.mem_filter.mp hi).2
  have hh := hp.2 hi'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Drift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem epsilon_nonneg (n Bmax : ℕ) : 0 ≤ epsilon n Bmax :=
  pow_nonneg (by norm_num) _

theorem centerUpdate_movement {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).All
      (fun q' => ∀ i, |q'.val i - q.val i| ≤ (I.D : ℤ)) := by
  unfold centerUpdate
  rw [RandomTree.all_bind]
  apply RandomTree.all_of_forall
  intro r₁
  rw [RandomTree.map, RandomTree.all_bind]
  apply RandomTree.all_of_forall
  intro r₂ i
  exact I.average_movement q (Int.natCast_nonneg _) r₁.property r₂.property i

theorem centerUpdate_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (q : BoxVector I) (hd : 2 * (I.D : ℤ) ≤ deviation G y q.val) :
    (centerUpdate P hR lower I hB q).probability (fun q' => ¬HighStep G I P y q q') ≤
      2 * epsilon G.n Bmax := by
  let K := I.narrowCentered hB q.val
  let u := centerSub y q.val (deviation G y q.val) I.D
  let bad := mass P.alpha (nearHigh G y q.val I.D) ≤ (4 / 5) * P.k
  have hu : AdmissibleSub (operator G) K.a K.b u P :=
    centered_admissible_high G I P hy q I.D (I.D_positive hB) (I.D_small.trans I.bounded) hd
  have hu₂ : AdmissibleSub (operator G) K.a K.b u P.reduceM := hu
  have hu₁ (hb : bad) : AdmissibleSub (operator G) K.a K.b u P.reduceK := by
    refine ⟨hu.1, ?_⟩
    change mass P.alpha (lowerActive (fun i => q.val i - I.D) u) ≤ (4 / 5) * P.k
    rw [show u = centerSub y q.val (deviation G y q.val) I.D from rfl, centered_active_high]
    exact hb
  have hh₂ := K.repeated_lower _ ((hLower P.reduceM (P.reduceM_rank hR)).1 K u hu₂)
    (globalJ_positive G.n Bmax)
  have hh₁ : (K.repeated (lower P.reduceK (P.reduceK_rank hR) K) (globalJ G.n Bmax)).probability
      (fun r => ¬(bad → u ≤ r.val)) ≤ epsilon G.n Bmax := by
    by_cases hb : bad
    · simpa only [hb, true_implies, epsilon] using
        K.repeated_lower _ ((hLower P.reduceK (P.reduceK_rank hR)).1 K u (hu₁ hb))
          (globalJ_positive G.n Bmax)
    · rw [RandomTree.probability_zero_of_all _
        (RandomTree.all_of_forall _ (fun r => by simp [hb]))]
      exact epsilon_nonneg _ _
  change ((_ : RandomTree (BoxVector K)).bind _).probability _ ≤ _
  apply le_trans (RandomTree.bind_error _ _ (fun r₁ => bad → u ≤ r₁.val) _
    (epsilon_nonneg _ _) hh₁ ?_) (by change epsilon G.n Bmax + epsilon G.n Bmax ≤ 2 * epsilon G.n Bmax; linarith)
  intro r₁ hr₁
  apply RandomTree.map_error _ _ (fun r₂ => u ≤ r₂.val) _ hh₂
  intro r₂ hr₂ hfail
  apply hfail
  constructor
  · apply deviation_le
    exact high_deviation_step hy.1.1.2 (by exact_mod_cast I.D_positive hB) hd
      (le_deviation G y q.val) r₁.property.1 hr₂
  · intro hb
    apply deviation_le
    exact high_bad_step hy.1.1.2 (by exact_mod_cast I.D_positive hB) hd (hr₁ hb) hr₂

theorem centerUpdate_low_deterministic (G : Game) {Bmax : ℕ}
    (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) {z : Vec (Fin G.n)}
    (hz : I.a ≤ z) (q : BoxVector I)
    (hd : 2 * (I.D : ℤ) ≤ deviation G q.val z)
    (r₁ r₂ : BoxVector (I.narrowCentered hB q.val))
    (hr₁ : r₁.val ≤ centerSuper z q.val (deviation G q.val z) I.D)
    (hr₂ : mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
      r₂.val ≤ centerSuper z q.val (deviation G q.val z) I.D) :
    LowStep G I P z q (I.averageClipped r₁.val r₂.val) := by
  have hD : (0 : ℤ) < I.D := by exact_mod_cast I.D_positive hB
  constructor
  · apply deviation_le
    exact low_deviation_step hz hD hd (le_deviation G q.val z) hr₁ r₂.property.2
  · intro hb
    apply deviation_le
    exact low_bad_step hz hD hd hr₁ (hr₂ hb)

theorem RandomTree.pair_error {α β γ : Type} (t₁ : RandomTree α) (t₂ : RandomTree β)
    (f : α → β → γ) (good₁ : α → Prop) (good₂ : β → Prop) (bad : γ → Prop)
    {ε : ℚ} (hε : 0 ≤ ε) (h₁ : t₁.probability (fun a => ¬good₁ a) ≤ ε)
    (h₂ : t₂.probability (fun b => ¬good₂ b) ≤ ε)
    (hf : ∀ a b, good₁ a → good₂ b → ¬bad (f a b)) :
    (t₁.bind fun a => t₂.map (f a)).probability bad ≤ 2 * ε := by
  apply le_trans (RandomTree.bind_error t₁ (fun a => t₂.map (f a)) good₁ bad hε h₁ ?_)
    (by exact le_of_eq (by ring))
  intro a ha
  exact RandomTree.map_error t₂ (f a) good₂ bad h₂ (fun b hb => hf a b ha hb)

theorem average_low_error (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : I.a ≤ z) (q : BoxVector I)
    (hd : 2 * (I.D : ℤ) ≤ deviation G q.val z)
    (t₁ t₂ : RandomTree (BoxVector (I.narrowCentered hB q.val))) {ε : ℚ} (hε : 0 ≤ ε)
    (h₁ : t₁.probability (fun r => ¬r.val ≤ centerSuper z q.val (deviation G q.val z) I.D) ≤ ε)
    (h₂ : t₂.probability (fun r => ¬(mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
      r.val ≤ centerSuper z q.val (deviation G q.val z) I.D)) ≤ ε) :
    (t₁.bind fun r₁ => t₂.map fun r₂ => I.averageClipped r₁.val r₂.val).probability
      (fun q' => ¬LowStep G I P z q q') ≤ 2 * ε := by
  apply RandomTree.pair_error t₁ t₂ (fun r₁ r₂ => I.averageClipped r₁.val r₂.val)
    (fun r₁ => r₁.val ≤ centerSuper z q.val (deviation G q.val z) I.D)
    (fun r₂ => mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
      r₂.val ≤ centerSuper z q.val (deviation G q.val z) I.D)
    (fun q' => ¬LowStep G I P z q q') hε h₁ h₂
  intro r₁ r₂ hr₁ hr₂ hfail
  exact hfail (centerUpdate_low_deterministic G P I hB hz q hd r₁ r₂ hr₁ hr₂)

theorem centerUpdate_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (q : BoxVector I) (hd : 2 * (I.D : ℤ) ≤ deviation G q.val z) :
    (centerUpdate P hR lower I hB q).probability (fun q' => ¬LowStep G I P z q q') ≤
      2 * epsilon G.n Bmax := by
  let K := I.narrowCentered hB q.val
  let u := centerSuper z q.val (deviation G q.val z) I.D
  let bad := mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m
  have hu : AdmissibleSuper (operator G) K.a K.b u P :=
    centered_admissible_low G I P hz q I.D (I.D_positive hB) (I.D_small.trans I.bounded) hd
  have hu₁ : AdmissibleSuper (operator G) K.a K.b u P.reduceK := hu
  have hu₂ (hb : bad) : AdmissibleSuper (operator G) K.a K.b u P.reduceM := by
    refine ⟨hu.1, ?_⟩
    change mass P.beta (upperActive (fun i => q.val i + I.D) u) ≤ (4 / 5) * P.m
    rw [show u = centerSuper z q.val (deviation G q.val z) I.D from rfl, centered_active_low]
    exact hb
  have hh₁ := K.repeated_upper _ ((hLower P.reduceK (P.reduceK_rank hR)).2 K u hu₁)
    (globalJ_positive G.n Bmax)
  have hh₂ : (K.repeated (lower P.reduceM (P.reduceM_rank hR) K) (globalJ G.n Bmax)).probability
      (fun r => ¬(bad → r.val ≤ u)) ≤ epsilon G.n Bmax := by
    by_cases hb : bad
    · simpa only [hb, true_implies, epsilon] using
        K.repeated_upper _ ((hLower P.reduceM (P.reduceM_rank hR)).2 K u (hu₂ hb))
          (globalJ_positive G.n Bmax)
    · rw [RandomTree.probability_zero_of_all _
        (RandomTree.all_of_forall _ (fun r => by simp [hb]))]
      exact epsilon_nonneg _ _
  exact average_low_error G P I hB hz.1.1.1 q hd _ _ (epsilon_nonneg _ _) hh₁ hh₂



theorem linked_single {α : Type} (R : α → α → Prop) (q : α) : Linked R q [q] := by
  simp [Linked]

theorem linked_cons {α : Type} {R : α → α → Prop} {q q' : α} {qs : List α}
    (h : R q q') (hs : Linked R q' qs) : Linked R q (q :: qs) := by
  refine ⟨rfl, hs.2.cons ?_⟩
  intro r hr
  rw [hs.1] at hr
  have : q' = r := Option.mem_some_iff.mp hr
  simpa [← this] using h

theorem centerDrift_start {n Bmax : ℕ} (I : SolveBox n Bmax) : CenterDrift I 0 I.midpoint := by
  intro i
  simp

theorem centerDrift_mono {n Bmax : ℕ} (I : SolveBox n Bmax) {r s : ℕ} (hrs : r ≤ s)
    {q : BoxVector I} (h : CenterDrift I r q) : CenterDrift I s q := by
  intro i
  exact (h i).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrs) (Int.natCast_nonneg _))

theorem centerDrift_move {n Bmax : ℕ} (I : SolveBox n Bmax) {r : ℕ} {q q' : BoxVector I}
    (h : CenterDrift I r q) (hmove : ∀ i, |q'.val i - q.val i| ≤ (I.D : ℤ)) :
    CenterDrift I (r + 1) q' := by
  intro i
  have hh := (abs_add_le (q'.val i - q.val i) (q.val i - I.midpoint.val i)).trans
    (add_le_add (hmove i) (h i))
  rw [show q'.val i - q.val i + (q.val i - I.midpoint.val i) =
      q'.val i - I.midpoint.val i by ring] at hh
  exact hh.trans_eq (by push_cast; ring)

theorem centerSteps_length {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).All (fun qs => qs.length = t + 1) := by
  induction t generalizing q with
  | zero => rfl
  | succ t ht =>
    rw [centerSteps, RandomTree.all_bind]
    apply RandomTree.all_of_forall
    intro q'
    rw [RandomTree.map, RandomTree.all_bind]
    exact RandomTree.all_mono _ (ht q') (fun qs hqs => by simpa [RandomTree.All] using hqs)

theorem centerSteps_relation {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (R : BoxVector I → BoxVector I → Prop)
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hstep : ∀ r q, r ≤ globalS Bmax → CenterDrift I r q →
      (centerUpdate P hR lower I hB q).probability (fun q' => ¬R q q') ≤ δ)
    (t r : ℕ) (q : BoxVector I) (hrt : r + t ≤ globalS Bmax) (hq : CenterDrift I r q) :
    (centerSteps P hR lower I hB t q).probability (fun qs => ¬Linked R q qs) ≤ t * δ := by
  induction t generalizing r q with
  | zero => simp [centerSteps, linked_single]
  | succ t ht =>
    have hm : (centerUpdate P hR lower I hB q).All (CenterDrift I (r + 1)) :=
      RandomTree.all_mono _ (centerUpdate_movement P hR lower I hB q)
        (fun q' hh => centerDrift_move I hq hh)
    have hp : (centerUpdate P hR lower I hB q).probability
        (fun q' => ¬ (R q q' ∧ CenterDrift I (r + 1) q')) ≤ δ := by
      apply le_trans _ (hstep r q (by omega) hq)
      apply RandomTree.probability_mono_all
      exact RandomTree.all_mono _ hm (fun q' hh hf hr => hf ⟨hr, hh⟩)
    rw [centerSteps]
    apply le_trans (RandomTree.bind_error _ _
      (fun q' => R q q' ∧ CenterDrift I (r + 1) q') _
      (mul_nonneg (Nat.cast_nonneg _) hδ) hp ?_) (by push_cast; ring_nf; rfl)
    intro q' hq'
    apply RandomTree.map_error _ _ (Linked R q') _
      (ht (r + 1) q' (by omega) hq'.2)
    intro qs hqs hf
    exact hf (linked_cons hq'.1 hqs)

theorem centerSteps_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (highCore I y).Nonempty) :
    (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
      (fun qs => ¬Linked (HighStep G I P y) I.midpoint qs) ≤
      2 * globalS Bmax * epsilon G.n Bmax := by
  have hh := centerSteps_relation P hR lower I hB (HighStep G I P y)
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (epsilon_nonneg G.n Bmax)) ?_
    (globalS Bmax) 0 I.midpoint (by omega) (centerDrift_start I)
  · convert hh using 1 ; ring
  intro r q hr hq
  apply centerUpdate_high G P hR lower hLower I hB hy q
  have hd := high_center_deviation G I hB hy.1.1.2 hc (centerDrift_mono I hr hq)
  have hde : I.D ≤ I.E := by
    have hs : 1 ≤ globalS Bmax := (show 1 ≤ 16 by omega).trans (globalS_large Bmax)
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans (I.radius_bounds hB).2.1
  have hde' : (I.D : ℤ) ≤ I.E := by exact_mod_cast hde
  omega

theorem centerSteps_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (lowCore I z).Nonempty) :
    (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
      (fun qs => ¬Linked (LowStep G I P z) I.midpoint qs) ≤
      2 * globalS Bmax * epsilon G.n Bmax := by
  have hh := centerSteps_relation P hR lower I hB (LowStep G I P z)
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (epsilon_nonneg G.n Bmax)) ?_
    (globalS Bmax) 0 I.midpoint (by omega) (centerDrift_start I)
  · convert hh using 1 ; ring
  intro r q hr hq
  apply centerUpdate_low G P hR lower hLower I hB hz q
  have hd := low_center_deviation G I hB hz.1.1.1 hc (centerDrift_mono I hr hq)
  have hde : I.D ≤ I.E := by
    have hs : 1 ≤ globalS Bmax := (show 1 ≤ 16 by omega).trans (globalS_large Bmax)
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans (I.radius_bounds hB).2.1
  have hde' : (I.D : ℤ) ≤ I.E := by exact_mod_cast hde
  omega

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Alternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
open scoped Classical

theorem linked_first {α : Type} {R : α → α → Prop} {q : α} {qs : List α}
    (h : Linked R q qs) : qs.getD 0 q = q := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h.1]
  rfl

theorem linked_step {α : Type} {R : α → α → Prop} {q : α} {qs : List α}
    (h : Linked R q qs) {j : ℕ} (hj : j + 1 < qs.length) :
    R (qs.getD j q) (qs.getD (j + 1) q) := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  exact List.isChain_iff_getElem.mp h.2 j hj

theorem badTimes_succ {α : Type} (bad : α → Prop) (qs : List α) (q : α) (t : ℕ) :
    badTimes bad qs q (t + 1) = badTimes bad qs q t + if bad (qs.getD t q) then 1 else 0 := by
  have hn : t ∉ (Finset.range t).filter (fun j => bad (qs.getD j q)) := by simp
  simp only [badTimes, Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> simp []

theorem linked_telescope {α : Type} (d : α → ℤ) (bad : α → Prop) (D : ℤ)
    {q : α} {qs : List α}
    (h : Linked (fun q q' => d q' ≤ d q ∧ (bad q → d q' ≤ d q - D)) q qs)
    {t : ℕ} (ht : t < qs.length) :
    d (qs.getD t q) + (badTimes bad qs q t : ℤ) * D ≤ d q := by
  induction t with
  | zero => rw [linked_first h]; simp
  | succ t ih =>
    have hi := ih (by omega)
    have hs := linked_step h ht
    rw [badTimes_succ]
    by_cases hb : bad (qs.getD t q)
    · simp only [hb, ite_true, if_true, Nat.cast_add, Nat.cast_one]
      nlinarith only [hi, hs.2 hb]
    · simp only [hb, ite_false, if_false, Nat.add_zero]
      linarith [hs.1]

theorem centerSteps_all_relation {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (R : BoxVector I → BoxVector I → Prop)
    (hstep : ∀ q, (centerUpdate P hR lower I hB q).All (R q))
    (t : ℕ) (q : BoxVector I) : (centerSteps P hR lower I hB t q).All (Linked R q) := by
  induction t generalizing q with
  | zero => exact linked_single R q
  | succ t ht =>
    rw [centerSteps, RandomTree.all_bind]
    apply RandomTree.all_mono _ (hstep q)
    intro q' hq'
    rw [RandomTree.map, RandomTree.all_bind]
    exact RandomTree.all_mono _ (ht q') (fun qs hqs => linked_cons hq' hqs)

theorem centerSteps_moving {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).All (Linked (Moving I) q) :=
  centerSteps_all_relation P hR lower I hB (Moving I)
    (centerUpdate_movement P hR lower I hB) t q

theorem centerSteps_metadata {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).All
      (fun qs => qs.length = t + 1 ∧ Linked (Moving I) q qs) := by
  apply RandomTree.all_and
  · exact centerSteps_length P hR lower I hB t q
  · exact centerSteps_moving P hR lower I hB t q

theorem linked_drift {n Bmax : ℕ} (I : SolveBox n Bmax) {qs : List (BoxVector I)}
    (h : Linked (Moving I) I.midpoint qs) {j : ℕ} (hj : j < qs.length) :
    CenterDrift I j (qs.getD j I.midpoint) := by
  induction j with
  | zero => rw [linked_first h]; exact centerDrift_start I
  | succ j ih => exact centerDrift_move I (ih (by omega)) (linked_step h hj)

theorem high_core_displacement (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {y : Vec (Fin G.n)}
    (hy : y ≤ I.b) {qs : List (BoxVector I)}
    (hlen : qs.length = globalS Bmax + 1) (h : Linked (HighStep G I P y) I.midpoint qs) :
    highCore I y ⊆ (NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ ∧
    (256 < badTimes (HighBad G I P y) qs I.midpoint (globalS Bmax) →
      highCore I y ⊆ PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint)) := by
  let q := qs.getD (globalS Bmax) I.midpoint
  let c := badTimes (HighBad G I P y) qs I.midpoint (globalS Bmax)
  have ht := linked_telescope (fun q : BoxVector I => deviation G y q.val)
    (HighBad G I P y) I.D h (by omega : globalS Bmax < qs.length)
  change deviation G y q.val + (c : ℤ) * I.D ≤ deviation G y I.midpoint.val at ht
  have hc : (0 : ℤ) ≤ c := Int.natCast_nonneg _
  have hD : (0 : ℤ) ≤ I.D := Int.natCast_nonneg _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hb : (128 : ℤ) * globalS Bmax < I.width := by exact_mod_cast hB
  have hn : deviation G y q.val ≤ deviation G y I.midpoint.val := by
    nlinarith only [ht, mul_nonneg hc hD]
  have hn' := mul_le_mul_of_nonneg_left hn hs
  have hdisp (i : Fin G.n) (hi : i ∈ highCore I y) :
      (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) ≥
      (globalS Bmax : ℤ) * (deviation G y I.midpoint.val - deviation G y q.val) -
        I.width - globalS Bmax := by
    have hi₀ := high_initial_deficit G I hy hi
    have hi₁ := mul_le_mul_of_nonneg_left (le_deviation G y q.val i) hs
    nlinarith only [hi₀, hi₁]
  constructor
  · intro i hi
    have hd := hdisp i hi
    simp only [Finset.mem_compl, NegativeDisplacement, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt]
    change -2 * (I.width : ℤ) ≤ (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i)
    nlinarith only [hd, hn', hb, hs]
  · intro hmore i hi
    have hd := hdisp i hi
    have hcnt : (257 : ℤ) ≤ c := by
      have hnat : 257 ≤ c := by omega
      exact_mod_cast hnat
    have ht' := mul_le_mul_of_nonneg_left ht hs
    have hcnt' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcnt hD) hs
    have hr : (I.width : ℤ) ≤ 64 * globalS Bmax * I.D := by
      exact_mod_cast (I.radius_bounds hB).1
    simp only [PositiveDisplacement, Finset.mem_filter, Finset.mem_univ, true_and]
    change 2 * (I.width : ℤ) < (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i)
    nlinarith only [hd, ht', hcnt', hr, hb, hs]

theorem low_core_displacement (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {z : Vec (Fin G.n)}
    (hz : I.a ≤ z) {qs : List (BoxVector I)}
    (hlen : qs.length = globalS Bmax + 1) (h : Linked (LowStep G I P z) I.midpoint qs) :
    lowCore I z ⊆ (PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ ∧
    (256 < badTimes (LowBad G I P z) qs I.midpoint (globalS Bmax) →
      lowCore I z ⊆ NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint)) := by
  let q := qs.getD (globalS Bmax) I.midpoint
  let c := badTimes (LowBad G I P z) qs I.midpoint (globalS Bmax)
  have ht := linked_telescope (fun q : BoxVector I => deviation G q.val z)
    (LowBad G I P z) I.D h (by omega : globalS Bmax < qs.length)
  change deviation G q.val z + (c : ℤ) * I.D ≤ deviation G I.midpoint.val z at ht
  have hc : (0 : ℤ) ≤ c := Int.natCast_nonneg _
  have hD : (0 : ℤ) ≤ I.D := Int.natCast_nonneg _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hb : (128 : ℤ) * globalS Bmax < I.width := by exact_mod_cast hB
  have hn : deviation G q.val z ≤ deviation G I.midpoint.val z := by
    nlinarith only [ht, mul_nonneg hc hD]
  have hn' := mul_le_mul_of_nonneg_left hn hs
  have hdisp (i : Fin G.n) (hi : i ∈ lowCore I z) :
      (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) ≤
      I.width + globalS Bmax -
        (globalS Bmax : ℤ) * (deviation G I.midpoint.val z - deviation G q.val z) := by
    have hi₀ := low_initial_deficit G I hz hi
    have hi₁ := mul_le_mul_of_nonneg_left (le_deviation G q.val z i) hs
    nlinarith only [hi₀, hi₁]
  constructor
  · intro i hi
    have hd := hdisp i hi
    simp only [Finset.mem_compl, PositiveDisplacement, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt]
    change (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) ≤ 2 * (I.width : ℤ)
    nlinarith only [hd, hn', hb, hs]
  · intro hmore i hi
    have hd := hdisp i hi
    have hcnt : (257 : ℤ) ≤ c := by
      have hnat : 257 ≤ c := by omega
      exact_mod_cast hnat
    have ht' := mul_le_mul_of_nonneg_left ht hs
    have hcnt' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcnt hD) hs
    have hr : (I.width : ℤ) ≤ 64 * globalS Bmax * I.D := by
      exact_mod_cast (I.radius_bounds hB).1
    simp only [NegativeDisplacement, Finset.mem_filter, Finset.mem_univ, true_and]
    change (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) < -2 * (I.width : ℤ)
    nlinarith only [hd, ht', hcnt', hr, hb, hs]

end MeanPayoff

namespace MeanPayoff
open scoped Classical

namespace RandomTree

theorem uniform_probability (k : ℕ) (P : ℕ → Prop) :
    (uniformBelow k).probability P =
      (((Finset.range (2 ^ k)).filter P).card : ℚ) / 2 ^ k := by
  unfold probability
  rw [expect_uniformBelow, Finset.card_filter]
  congr 1
  simp

theorem sample_badTimes {α : Type} (Bmax : ℕ) (P : α → Prop) (qs : List α) (q : α)
    (h : badTimes P qs q (globalS Bmax) ≤ 256) :
    (uniformBelow (sampleExponent Bmax)).probability (fun j => P (qs.getD j q)) ≤
      256 / (globalS Bmax : ℚ) := by
  rw [uniform_probability]
  have hden : (2 : ℚ) ^ sampleExponent Bmax = (globalS Bmax : ℚ) := by
    simp only [globalS, Nat.cast_pow, Nat.cast_ofNat]
  rw [hden]
  change (badTimes P qs q (globalS Bmax) : ℚ) / (globalS Bmax : ℚ) ≤ _
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg _)

end RandomTree

theorem nearHigh_child_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (y : Vec (Fin G.n)) (q : BoxVector I) :
    nearHigh G y q.val I.D ⊆
      highCore (I.wideCentered hB q.val) (centerSub y q.val (deviation G y q.val) I.E) := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hu : y i - deviation G y q.val + I.E ≤
      centerSub y q.val (deviation G y q.val) I.E i := le_max_left _ _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hd : (globalS Bmax : ℤ) * I.D ≤ I.E := by exact_mod_cast (I.radius_bounds hB).2.1
  have hh : q.val i + I.E - 2 * I.D ≤ centerSub y q.val (deviation G y q.val) I.E i := by
    omega
  have hm := mul_le_mul_of_nonneg_left hh hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (globalS Bmax : ℤ) * ↑(2 * I.E) - ↑(2 * I.E) ≤
    (globalS Bmax : ℤ) * (centerSub y q.val (deviation G y q.val) I.E i - (q.val i - I.E))
  push_cast
  nlinarith only [hm, hd]

theorem nearLow_child_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (z : Vec (Fin G.n)) (q : BoxVector I) :
    nearLow G z q.val I.D ⊆
      lowCore (I.wideCentered hB q.val) (centerSuper z q.val (deviation G q.val z) I.E) := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hu : centerSuper z q.val (deviation G q.val z) I.E i ≤
      z i + deviation G q.val z - I.E := min_le_left _ _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hd : (globalS Bmax : ℤ) * I.D ≤ I.E := by exact_mod_cast (I.radius_bounds hB).2.1
  have hh : centerSuper z q.val (deviation G q.val z) I.E i ≤ q.val i - I.E + 2 * I.D := by
    omega
  have hm := mul_le_mul_of_nonneg_left hh hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (globalS Bmax : ℤ) * ↑(2 * I.E) - ↑(2 * I.E) ≤
    (globalS Bmax : ℤ) * ((q.val i + I.E) - centerSuper z q.val (deviation G q.val z) I.E i)
  push_cast
  nlinarith only [hm, hd]

theorem alternative_mono {n : ℕ} {P : Budgets n} {side : Bool} {w : Fin n → ℚ}
    (hw : ∀ i, 0 ≤ w i) {S T : Finset (Fin n)} {budget : ℚ} {O O' : Orientation P}
    (hst : S ⊆ T) (hs : O'.chooseY = O.chooseY) (hl : ∀ H ∈ O.exceptions, H ∈ O'.exceptions)
    (h : Alternative side w S budget O) : Alternative side w T budget O' := by
  rcases h with h | ⟨H, hH, hm⟩
  · exact Or.inl (hs.trans h)
  · refine Or.inr ⟨H, hl H hH, hm.trans_le ?_⟩
    apply mass_mono hw
    intro i hi
    exact Finset.mem_inter.mpr ⟨hst (Finset.mem_inter.mp hi).1, (Finset.mem_inter.mp hi).2⟩

theorem alternative_witness {n : ℕ} {P : Budgets n} {side : Bool} {w : Fin n → ℚ}
    (hw : ∀ i, 0 ≤ w i) {S Core : Finset (Fin n)} {budget : ℚ} {O : Orientation P}
    (hc : (4 / 5) * budget < mass w Core) (hcs : Core ⊆ S)
    (H : SmallSet P) (hH : H ∈ O.exceptions) (h : Core ⊆ H.val) :
    Alternative side w S budget O := by
  refine Or.inr ⟨H, hH, hc.trans_le (mass_mono hw ?_)⟩
  exact Finset.subset_inter hcs h

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Orientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
open scoped Classical

theorem high_core_exact_half (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : Subsolution (operator G) I.a I.b y) :
    highCore I y ⊆ Finset.univ.filter
      (fun i => (I.width : ℤ) ≤ 2 * ((I.exactVector G).val i - I.a i)) := by
  have hp : y ≤ (I.exactVector G).val := box_comparison G hy (basic_spec G I.a I.b I.ordered).2.1
  intro i hi
  have hic := (Finset.mem_filter.mp hi).2
  have hpi : y i ≤ (I.exactVector G).val i := hp i
  have hyi : y i ≤ I.b i := hy.1.2 i
  have hw := I.width_bound i
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hd : 0 ≤ (I.width : ℤ) - (y i - I.a i) := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hs) hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  nlinarith only [hic, hm, hb, hpi]

theorem low_core_exact_half (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : Supersolution (operator G) I.a I.b z) :
    lowCore I z ⊆ (Finset.univ.filter
      (fun i => (I.width : ℤ) ≤ 2 * ((I.exactVector G).val i - I.a i)))ᶜ := by
  have hp : (I.exactVector G).val ≤ z := box_comparison G (basic_spec G I.a I.b I.ordered).1 hz
  intro i hi
  have hic := (Finset.mem_filter.mp hi).2
  have hpi : (I.exactVector G).val i ≤ z i := hp i
  have hzi : I.a i ≤ z i := hz.1.1 i
  have hw := I.width_bound i
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hd : 0 ≤ (I.width : ℤ) - (I.b i - z i) := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hs) hd
  simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  nlinarith only [hic, hm, hb, hpi, hw]

theorem orientBase_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    HighAlternative I P y (orientBase G P I) := by
  unfold orientBase
  dsimp only
  split_ifs with h
  · exact Or.inl rfl
  · apply alternative_witness (fun i => (P.alpha_pos i).le) hc (highCore_support I y)
      ⟨_, le_of_not_gt h⟩ (by simp) (high_core_exact_half G I hy.1)

theorem orientBase_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    LowAlternative I P z (orientBase G P I) := by
  unfold orientBase
  dsimp only
  split_ifs with h
  · apply alternative_witness (fun i => (P.beta_pos i).le) hc (lowCore_support I z)
      ⟨_, by rw [P.measure_compl G.positive]; linarith only [h]⟩
      (by simp) (low_core_exact_half G I hz.1)
  · exact Or.inl rfl

theorem core_nonempty {n : ℕ} {w : Fin n → ℚ} {C : Finset (Fin n)} {b : ℚ}
    (hb : 0 < b) (hc : (4 / 5) * b < mass w C) : C.Nonempty := by
  by_contra hn
  have hC : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [hC, mass, Finset.sum_empty] at hc
  linarith only [hb, hc]

theorem orient_high_support_transfer (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {y : Vec (Fin G.n)}
    (hy : AdmissibleSub (operator G) I.a I.b y P) (q : BoxVector I)
    (hd : 2 * (I.E : ℤ) ≤ deviation G y q.val) {O : Orientation P}
    (h : HighAlternative (I.wideCentered hB q.val) P
      (centerSub y q.val (deviation G y q.val) I.E) O) : HighAlternative I P y O := by
  have hp := centered_subsolution (operator_laws G) hy.1 q.property
    (show (0 : ℤ) < I.E by exact_mod_cast I.E_positive hB) (le_deviation G y q.val) hd
  apply alternative_mono (fun i => (P.alpha_pos i).le) ?_ rfl (fun _ => id) h
  intro i hi
  have hi' : i ∈ subSupport (fun i => q.val i - I.E)
      (centerSub y q.val (deviation G y q.val) I.E) := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 hi'⟩

theorem orient_low_support_transfer (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {z : Vec (Fin G.n)}
    (hz : AdmissibleSuper (operator G) I.a I.b z P) (q : BoxVector I)
    (hd : 2 * (I.E : ℤ) ≤ deviation G q.val z) {O : Orientation P}
    (h : LowAlternative (I.wideCentered hB q.val) P
      (centerSuper z q.val (deviation G q.val z) I.E) O) : LowAlternative I P z O := by
  have hp := centered_supersolution (operator_laws G) hz.1 q.property
    (show (0 : ℤ) < I.E by exact_mod_cast I.E_positive hB) (le_deviation G q.val z) hd
  apply alternative_mono (fun i => (P.beta_pos i).le) ?_ rfl (fun _ => id) h
  intro i hi
  have hi' : i ∈ superSupport (fun i => q.val i + I.E)
      (centerSuper z q.val (deviation G q.val z) I.E) := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 hi'⟩

end MeanPayoff

namespace MeanPayoff
open scoped Classical

theorem RandomTree.failure_zero {α : Type} (t : RandomTree α) {P : α → Prop}
    (h : t.All P) : t.probability (fun a => ¬P a) = 0 :=
  probability_zero_of_all t (all_mono t h (fun _ ha hna => hna ha))

theorem orientationTail_high (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y))
    (qs : List (BoxVector I)) (hlen : qs.length = globalS Bmax + 1)
    (hpath : Linked (HighStep G I P y) I.midpoint qs)
    (child : BoxVector I → RandomTree (Orientation P)) {δ : ℚ} (hδ : 0 ≤ δ)
    (hchild : ∀ j, j < globalS Bmax → ¬HighBad G I P y (qs.getD j I.midpoint) →
      (child (qs.getD j I.midpoint)).probability (fun O => ¬HighAlternative I P y O) ≤ δ) :
    (orientationTail G P I qs child).probability (fun O => ¬HighAlternative I P y O) ≤
      256 / (globalS Bmax : ℚ) + δ := by
  have hn : (0 : ℚ) ≤ 256 / (globalS Bmax : ℚ) + δ :=
    add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ
  have hd := high_core_displacement G I P hB hy.1.1.2 hlen hpath
  unfold orientationTail
  dsimp only
  split_ifs with hH hN
  · rw [RandomTree.probability_leaf]
    split_ifs with hf
    · exact hn
    · exact (hf (Or.inl rfl)).elim
  · have hok : HighAlternative I P y
        ⟨false, [⟨(NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ,
          by rw [P.measure_compl G.positive]; linarith only [hN]⟩]⟩ := by
      apply alternative_witness (fun i => (P.alpha_pos i).le) hc (highCore_support I y)
        ⟨_, by rw [P.measure_compl G.positive]; linarith only [hN]⟩ (by simp) hd.1
    rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
    exact hn
  · by_cases hmore : 256 < badTimes (HighBad G I P y) qs I.midpoint (globalS Bmax)
    · rw [RandomTree.failure_zero _ ?_]
      · exact hn
      rw [RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro j
      rw [RandomTree.map, RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro O
      apply alternative_witness (fun i => (P.alpha_pos i).le) hc (highCore_support I y)
        ⟨PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint), le_of_not_gt hH⟩
        (by simp) (hd.2 hmore)
    · have hsamp : (RandomTree.uniformBelow (sampleExponent Bmax)).probability
          (fun j => ¬(j < globalS Bmax ∧ ¬HighBad G I P y (qs.getD j I.midpoint))) ≤
          256 / (globalS Bmax : ℚ) := by
        apply le_trans _ (RandomTree.sample_badTimes Bmax (HighBad G I P y) qs I.midpoint
          (Nat.le_of_not_gt hmore))
        apply RandomTree.probability_mono_all
        apply RandomTree.all_mono _ (RandomTree.uniformBelow_lt (sampleExponent Bmax))
        intro j hj hfail
        by_contra hb
        exact hfail ⟨hj, hb⟩
      apply RandomTree.bind_error _ _
        (fun j => j < globalS Bmax ∧ ¬HighBad G I P y (qs.getD j I.midpoint)) _ hδ hsamp
      intro j hj
      apply RandomTree.map_error _ _ (HighAlternative I P y) _ (hchild j hj.1 hj.2)
      intro O hO hfail
      apply hfail
      exact alternative_mono (O := O) (fun i => (P.alpha_pos i).le) (Finset.Subset.refl _)
        rfl (fun H hH => List.mem_append_left _ hH) (show Alternative _ _ _ _ O from hO)

theorem orientationTail_low (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z))
    (qs : List (BoxVector I)) (hlen : qs.length = globalS Bmax + 1)
    (hpath : Linked (LowStep G I P z) I.midpoint qs)
    (child : BoxVector I → RandomTree (Orientation P)) {δ : ℚ} (hδ : 0 ≤ δ)
    (hchild : ∀ j, j < globalS Bmax → ¬LowBad G I P z (qs.getD j I.midpoint) →
      (child (qs.getD j I.midpoint)).probability (fun O => ¬LowAlternative I P z O) ≤ δ) :
    (orientationTail G P I qs child).probability (fun O => ¬LowAlternative I P z O) ≤
      256 / (globalS Bmax : ℚ) + δ := by
  have hn : (0 : ℚ) ≤ 256 / (globalS Bmax : ℚ) + δ :=
    add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ
  have hd := low_core_displacement G I P hB hz.1.1.1 hlen hpath
  unfold orientationTail
  dsimp only
  split_ifs with hH hN
  · have hok : LowAlternative I P z
        ⟨true, [⟨(PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ,
          by rw [P.measure_compl G.positive]; linarith only [hH]⟩]⟩ := by
      apply alternative_witness (fun i => (P.beta_pos i).le) hc (lowCore_support I z)
        ⟨_, by rw [P.measure_compl G.positive]; linarith only [hH]⟩ (by simp) hd.1
    rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
    exact hn
  · rw [RandomTree.probability_leaf]
    split_ifs with hf
    · exact hn
    · exact (hf (Or.inl rfl)).elim
  · by_cases hmore : 256 < badTimes (LowBad G I P z) qs I.midpoint (globalS Bmax)
    · rw [RandomTree.failure_zero _ ?_]
      · exact hn
      rw [RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro j
      rw [RandomTree.map, RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro O
      apply alternative_witness (fun i => (P.beta_pos i).le) hc (lowCore_support I z)
        ⟨NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint), le_of_not_gt hN⟩
        (by simp) (hd.2 hmore)
    · have hsamp : (RandomTree.uniformBelow (sampleExponent Bmax)).probability
          (fun j => ¬(j < globalS Bmax ∧ ¬LowBad G I P z (qs.getD j I.midpoint))) ≤
          256 / (globalS Bmax : ℚ) := by
        apply le_trans _ (RandomTree.sample_badTimes Bmax (LowBad G I P z) qs I.midpoint
          (Nat.le_of_not_gt hmore))
        apply RandomTree.probability_mono_all
        apply RandomTree.all_mono _ (RandomTree.uniformBelow_lt (sampleExponent Bmax))
        intro j hj hfail
        by_contra hb
        exact hfail ⟨hj, hb⟩
      apply RandomTree.bind_error _ _
        (fun j => j < globalS Bmax ∧ ¬LowBad G I P z (qs.getD j I.midpoint)) _ hδ hsamp
      intro j hj
      apply RandomTree.map_error _ _ (LowAlternative I P z) _ (hchild j hj.1 hj.2)
      intro O hO hfail
      apply hfail
      exact alternative_mono (O := O) (fun i => (P.beta_pos i).le) (Finset.Subset.refl _)
        rfl (fun H hH => List.mem_append_left _ hH) (show Alternative _ _ _ _ O from hO)

end MeanPayoff

namespace MeanPayoff

theorem orientationError_nonneg (n Bmax : ℕ) : 0 ≤ orientationError n Bmax :=
  add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (epsilon_nonneg n Bmax))

theorem clog_double_decrease {B C : ℕ} (hB : 1 < B) (hC : 2 * C ≤ B) :
    Nat.clog 2 C + 1 ≤ Nat.clog 2 B := by
  have hp := Nat.le_pow_clog (by norm_num : 1 < 2) B
  cases hk : Nat.clog 2 B with
  | zero => simp only [hk, pow_zero] at hp; omega
  | succ k =>
    rw [hk, pow_succ] at hp
    have hc : C ≤ 2 ^ k := by omega
    have hh := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hc
    omega

theorem orientation_error_step (n Bmax : ℕ) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    2 * globalS Bmax * epsilon n Bmax +
      (256 / (globalS Bmax : ℚ) + (Nat.clog 2 (2 * I.E) : ℚ) * orientationError n Bmax) ≤
      (Nat.clog 2 I.width : ℚ) * orientationError n Bmax := by
  have hs := globalS_large Bmax
  have hr := (I.radius_bounds hB).2.2.2
  have hh := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
  have hh' : (Nat.clog 2 (2 * I.E) : ℚ) + 1 ≤ Nat.clog 2 I.width := by exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_right hh' (orientationError_nonneg n Bmax)
  calc
    _ = ((Nat.clog 2 (2 * I.E) : ℚ) + 1) * orientationError n Bmax := by
      unfold orientationError
      ring
    _ ≤ _ := hm

theorem RandomTree.failure_with_metadata {α : Type} (t : RandomTree α)
    (A B C : α → Prop) (h : t.All (fun a => A a ∧ B a)) :
    t.probability (fun a => ¬(A a ∧ B a ∧ C a)) ≤ t.probability (fun a => ¬C a) := by
  apply probability_mono_all
  exact all_mono t h (fun a hh hf hc => hf ⟨hh.1, hh.2, hc⟩)

theorem orient_high_bound (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    (orient G P hR lower I).probability (fun O => ¬HighAlternative I P y O) ≤
      (Nat.clog 2 I.width : ℚ) * orientationError G.n Bmax := by
  induction I using (measure (fun I : SolveBox G.n Bmax => I.width)).wf.induction generalizing y with
  | h I ih =>
      by_cases hsmall : I.width ≤ 128 * globalS Bmax
      · rw [orient, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro (orientBase_high G P I hy hc))]
        exact mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
      · have hB : 128 * globalS Bmax < I.width := Nat.lt_of_not_ge hsmall
        rw [orient, dite_eq_right hsmall]
        dsimp only
        have hcore := core_nonempty P.k_pos hc
        have hp : (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
            (fun qs => ¬(qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
              Linked (HighStep G I P y) I.midpoint qs)) ≤ 2 * globalS Bmax * epsilon G.n Bmax := by
          apply le_trans _ (centerSteps_high G P hR lower hLower I hB hy hcore)
          with_reducible
            exact RandomTree.failure_with_metadata
              (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
              (fun qs => qs.length = globalS Bmax + 1)
              (Linked (Moving I) I.midpoint) (Linked (HighStep G I P y) I.midpoint)
              (centerSteps_metadata P hR lower I hB (globalS Bmax) I.midpoint)
        let δ := (Nat.clog 2 (2 * I.E) : ℚ) * orientationError G.n Bmax
        have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
        apply le_trans (RandomTree.bind_error
          (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
          (fun qs => orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hB q.val)))
          (fun qs => qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
            Linked (HighStep G I P y) I.midpoint qs) (fun O => ¬HighAlternative I P y O)
          (ε := 256 / (globalS Bmax : ℚ) + δ)
          (add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ) hp ?_)
          (orientation_error_step G.n Bmax I hB)
        intro qs hqs
        apply orientationTail_high G P I hB hy hc qs hqs.1 hqs.2.2 _ hδ
        intro j hj hbad
        let q := qs.getD j I.midpoint
        have hq : CenterDrift I (globalS Bmax) q :=
          centerDrift_mono I hj.le (linked_drift I hqs.2.1 (by omega))
        have hd := high_center_deviation G I hB hy.1.1.2 hcore hq
        let K := I.wideCentered hB q.val
        let u := centerSub y q.val (deviation G y q.val) I.E
        have hu : AdmissibleSub (operator G) K.a K.b u P :=
          centered_admissible_high G I P hy q I.E (I.E_positive hB) (I.E_smaller.le.trans I.bounded) hd
        have huc : (4 / 5) * P.k < mass P.alpha (highCore K u) :=
          (lt_of_not_ge hbad).trans_le (mass_mono (fun i => (P.alpha_pos i).le)
            (nearHigh_child_core G I hB y q))
        apply le_trans _ (ih K (by exact I.E_smaller) u hu huc)
        exact RandomTree.probability_mono _ (fun O hf hu => hf
          (orient_high_support_transfer G I P hB hy q hd hu))

theorem orient_low_bound (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    (orient G P hR lower I).probability (fun O => ¬LowAlternative I P z O) ≤
      (Nat.clog 2 I.width : ℚ) * orientationError G.n Bmax := by
  induction I using (measure (fun I : SolveBox G.n Bmax => I.width)).wf.induction generalizing z with
  | h I ih =>
      by_cases hsmall : I.width ≤ 128 * globalS Bmax
      · rw [orient, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro (orientBase_low G P I hz hc))]
        exact mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
      · have hB : 128 * globalS Bmax < I.width := Nat.lt_of_not_ge hsmall
        rw [orient, dite_eq_right hsmall]
        dsimp only
        have hcore := core_nonempty P.m_pos hc
        have hp : (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
            (fun qs => ¬(qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
              Linked (LowStep G I P z) I.midpoint qs)) ≤ 2 * globalS Bmax * epsilon G.n Bmax := by
          apply le_trans _ (centerSteps_low G P hR lower hLower I hB hz hcore)
          with_reducible
            exact RandomTree.failure_with_metadata
              (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
              (fun qs => qs.length = globalS Bmax + 1)
              (Linked (Moving I) I.midpoint) (Linked (LowStep G I P z) I.midpoint)
              (centerSteps_metadata P hR lower I hB (globalS Bmax) I.midpoint)
        let δ := (Nat.clog 2 (2 * I.E) : ℚ) * orientationError G.n Bmax
        have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
        apply le_trans (RandomTree.bind_error
          (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
          (fun qs => orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hB q.val)))
          (fun qs => qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
            Linked (LowStep G I P z) I.midpoint qs) (fun O => ¬LowAlternative I P z O)
          (ε := 256 / (globalS Bmax : ℚ) + δ)
          (add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ) hp ?_)
          (orientation_error_step G.n Bmax I hB)
        intro qs hqs
        apply orientationTail_low G P I hB hz hc qs hqs.1 hqs.2.2 _ hδ
        intro j hj hbad
        let q := qs.getD j I.midpoint
        have hq : CenterDrift I (globalS Bmax) q :=
          centerDrift_mono I hj.le (linked_drift I hqs.2.1 (by omega))
        have hd := low_center_deviation G I hB hz.1.1.1 hcore hq
        let K := I.wideCentered hB q.val
        let u := centerSuper z q.val (deviation G q.val z) I.E
        have hu : AdmissibleSuper (operator G) K.a K.b u P :=
          centered_admissible_low G I P hz q I.E (I.E_positive hB) (I.E_smaller.le.trans I.bounded) hd
        have huc : (4 / 5) * P.m < mass P.beta (lowCore K u) :=
          (lt_of_not_ge hbad).trans_le (mass_mono (fun i => (P.beta_pos i).le)
            (nearLow_child_core G I hB z q))
        apply le_trans _ (ih K (by exact I.E_smaller) u hu huc)
        exact RandomTree.probability_mono _ (fun O hf hu => hf
          (orient_low_support_transfer G I P hB hz q hd hu))

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Tightening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem globalJ_quadratic (n Bmax : ℕ) : 2 * globalS Bmax ^ 2 ≤ globalJ n Bmax := by
  have hs : 1 ≤ globalS Bmax := le_trans (by norm_num) (globalS_large Bmax)
  have hx : globalS Bmax ≤ globalS Bmax * (n + 1) := by nlinarith
  have hpow : globalS Bmax ^ 2 ≤ globalS Bmax ^ 6 :=
    pow_le_pow_right₀ hs (by norm_num)
  have hpow' := Nat.pow_le_pow_left hx 6
  unfold globalJ
  omega

theorem geometric_error (k : ℕ) (hk : 16 ≤ k) :
    (k : ℚ) * (1 / 2 : ℚ) ^ k ≤ 1 / 4096 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : 0 ≤ (1 / 2 : ℚ) ^ k := pow_nonneg (by norm_num) _
    have hkk : 1 ≤ (k : ℚ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hm := mul_nonneg (sub_nonneg.mpr hkk) hp
    rw [pow_succ]
    push_cast
    nlinarith only [hm, ih]

theorem orientation_error_small (n Bmax : ℕ) :
    ((globalG Bmax + 1 : ℕ) : ℚ) * orientationError n Bmax ≤ 1 / 16 := by
  have hs := globalS_lower Bmax
  have hslarge := globalS_large Bmax
  have hJ := globalJ_quadratic n Bmax
  have hsg : globalG Bmax + 1 ≤ globalS Bmax := by omega
  have hprod : 2 * (globalG Bmax + 1) * globalS Bmax ≤ globalJ n Bmax := by
    nlinarith only [hJ, hsg]
  have hJlarge : 16 ≤ globalJ n Bmax := by nlinarith only [hJ, hslarge]
  have hspos : (0 : ℚ) < globalS Bmax := by exact_mod_cast (show 0 < globalS Bmax by omega)
  have hs' : (131072 : ℚ) * (globalG Bmax + 1) ≤ globalS Bmax := by exact_mod_cast hs
  have hfirst : ((globalG Bmax + 1 : ℕ) : ℚ) * (256 / (globalS Bmax : ℚ)) ≤ 1 / 512 := by
    rw [← mul_div_assoc, div_le_iff₀ hspos]
    push_cast
    linarith only [hs']
  have hp' : (2 : ℚ) * (globalG Bmax + 1) * globalS Bmax ≤ globalJ n Bmax := by
    exact_mod_cast hprod
  have hsecond := mul_le_mul_of_nonneg_right hp' (epsilon_nonneg n Bmax)
  have hge := geometric_error (globalJ n Bmax) hJlarge
  change (globalJ n Bmax : ℚ) * epsilon n Bmax ≤ 1 / 4096 at hge
  unfold orientationError
  push_cast at hfirst ⊢
  nlinarith only [hfirst, hsecond, hge]

theorem orient_high_small (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    (orient G P hR lower I).probability (fun O => ¬HighAlternative I P y O) ≤ 1 / 16 := by
  apply le_trans (orient_high_bound G P hR lower hLower I y hy hc)
  apply le_trans _ (orientation_error_small G.n Bmax)
  apply mul_le_mul_of_nonneg_right _ (orientationError_nonneg _ _)
  have hc := Nat.clog_mono_right 2 (I.bounded.trans (Nat.le_succ Bmax))
  change Nat.clog 2 I.width ≤ Nat.clog 2 (Bmax + 1) at hc
  unfold globalG
  exact_mod_cast (show Nat.clog 2 I.width ≤ 1 + Nat.clog 2 (Bmax + 1) + 1 by omega)

theorem orient_low_small (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    (orient G P hR lower I).probability (fun O => ¬LowAlternative I P z O) ≤ 1 / 16 := by
  apply le_trans (orient_low_bound G P hR lower hLower I z hz hc)
  apply le_trans _ (orientation_error_small G.n Bmax)
  apply mul_le_mul_of_nonneg_right _ (orientationError_nonneg _ _)
  have hc := Nat.clog_mono_right 2 (I.bounded.trans (Nat.le_succ Bmax))
  change Nat.clog 2 I.width ≤ Nat.clog 2 (Bmax + 1) at hc
  unfold globalG
  exact_mod_cast (show Nat.clog 2 I.width ≤ 1 + Nat.clog 2 (Bmax + 1) + 1 by omega)


open scoped Classical

theorem RandomTree.filter_le_badCount {α : Type} (P : α → Prop) (p : α → Bool)
    (as : List α) (h : ∀ a ∈ as, p a = true → ¬ P a) :
    (as.filter p).length ≤ badCount P as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    by_cases ha : p a = true
    · have hn := h a (List.mem_cons_self ..) ha
      simp only [List.filter_cons, ha, ↓reduceIte, List.length_cons, badCount, ite_eq_right hn]
      omega
    · have hfalse : p a = false := Bool.eq_false_iff.mpr ha
      simp only [List.filter_cons, hfalse, Bool.false_eq_true, ↓reduceIte, badCount]
      split_ifs <;> omega

theorem bool_filter_partition {α : Type} (as : List α) (p : α → Bool) :
    (as.filter p).length + (as.filter (fun a => !p a)).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : p a <;> simp only [List.filter_cons, h, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem exception_retained {n : ℕ} {P : Budgets n} (os : List (Orientation P))
    {O : Orientation P} (hO : O ∈ os) {H : SmallSet P} (hH : H ∈ O.exceptions) :
    H ∈ (combineOrientations os).exceptions := by
  exact List.mem_flatten.mpr ⟨O.exceptions, List.mem_map.mpr ⟨O, hO, rfl⟩, hH⟩

theorem combine_high_failure {n : ℕ} {P : Budgets n} (w : Fin n → ℚ)
    (S : Finset (Fin n)) (b : ℚ) (os : List (Orientation P))
    (hf : ¬ Alternative true w S b (combineOrientations os)) :
    os.length ≤ 2 * RandomTree.badCount (Alternative true w S b) os := by
  have hc : 2 * (os.filter (fun o => o.chooseY)).length ≤ os.length := by
    by_contra hn
    apply hf
    exact Or.inl (by simp [combineOrientations, Nat.lt_of_not_ge hn])
  have hb := RandomTree.filter_le_badCount (Alternative true w S b) (fun o => !o.chooseY) os
    (by
      intro O hO hn hgood
      rcases hgood with hside | ⟨H, hH, hm⟩
      · simp [hside] at hn
      · exact hf (Or.inr ⟨H, exception_retained os hO hH, hm⟩))
  have hp := bool_filter_partition os (fun o => o.chooseY)
  omega

theorem combine_low_failure {n : ℕ} {P : Budgets n} (w : Fin n → ℚ)
    (S : Finset (Fin n)) (b : ℚ) (os : List (Orientation P))
    (hf : ¬ Alternative false w S b (combineOrientations os)) :
    os.length ≤ 2 * RandomTree.badCount (Alternative false w S b) os := by
  have hc : os.length < 2 * (os.filter (fun o => o.chooseY)).length := by
    by_contra hn
    apply hf
    exact Or.inl (by simp [combineOrientations, hn])
  have hb := RandomTree.filter_le_badCount (Alternative false w S b) (fun o => o.chooseY) os
    (by
      intro O hO hn hgood
      rcases hgood with hside | ⟨H, hH, hm⟩
      · simp [hside] at hn
      · exact hf (Or.inr ⟨H, exception_retained os hO hH, hm⟩))
  omega

theorem orientPlus_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    (orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).probability
      (fun O => ¬HighAlternative I P y O) ≤ epsilon G.n Bmax := by
  rw [orientPlus, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification _ (HighAlternative I P y)
    (orient_high_small G P hR lower hLower I y hy hc) (globalJ G.n Bmax))
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length _ _)
  intro os hlen hf
  rw [← hlen]
  exact combine_high_failure P.alpha (lowerActive I.a y) P.k os hf

theorem orientPlus_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    (orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).probability
      (fun O => ¬LowAlternative I P z O) ≤ epsilon G.n Bmax := by
  rw [orientPlus, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification _ (LowAlternative I P z)
    (orient_low_small G P hR lower hLower I z hz hc) (globalJ G.n Bmax))
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length _ _)
  intro os hlen hf
  rw [← hlen]
  exact combine_low_failure P.beta (upperActive I.b z) P.m os hf

end MeanPayoff

namespace MeanPayoff
open scoped Classical

theorem AdmissibleSub.raise_floor {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {P : Budgets n} {a b a' y : Vec (Fin n)}
    (hy : AdmissibleSub F a b y P) (haa' : a ≤ a') (ha'b : a' ≤ b) :
    AdmissibleSub F a' b (fun i => max (y i) (a' i)) P := by
  have hp := subsolution_raise_floor laws hy.1 haa' ha'b
  refine ⟨hp.1, (mass_mono (fun i => (P.alpha_pos i).le) ?_).trans hy.2⟩
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 (Finset.mem_filter.mp hi).2⟩

theorem AdmissibleSuper.lower_ceiling {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {P : Budgets n} {a b b' z : Vec (Fin n)}
    (hz : AdmissibleSuper F a b z P) (hab' : a ≤ b') (hb'b : b' ≤ b) :
    AdmissibleSuper F a b' (fun i => min (z i) (b' i)) P := by
  have hp := supersolution_lower_ceiling laws hz.1 hab' hb'b
  refine ⟨hp.1, (mass_mono (fun i => (P.beta_pos i).le) ?_).trans hz.2⟩
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 (Finset.mem_filter.mp hi).2⟩

theorem AdmissibleSub.restrict_ceiling {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b b' y : Vec (Fin n)}
    (hy : AdmissibleSub F a b y P) (hyb' : y ≤ b') : AdmissibleSub F a b' y P :=
  ⟨⟨⟨hy.1.1.1, hyb'⟩, hy.1.2⟩, hy.2⟩

theorem AdmissibleSuper.restrict_floor {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b a' z : Vec (Fin n)}
    (hz : AdmissibleSuper F a b z P) (ha'z : a' ≤ z) : AdmissibleSuper F a' b z P :=
  ⟨⟨⟨ha'z, hz.1.1.2⟩, hz.1.2⟩, hz.2⟩

theorem SolveBox.delta_bounds {n Bmax : ℕ} (I : SolveBox n Bmax) :
    4 * globalS Bmax * I.delta ≤ I.width ∧ I.delta ≤ I.C := by
  have hd := Nat.div_mul_le_self I.width (4 * globalS Bmax)
  have hs := globalS_large Bmax
  constructor
  · simpa only [mul_comm, SolveBox.delta] using hd
  · change I.width / (4 * globalS Bmax) ≤ I.width - I.width / (4 * globalS Bmax)
    have hh : 2 * (I.width / (4 * globalS Bmax)) ≤ I.width := by nlinarith
    omega

theorem tightSub_solution (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : Subsolution (operator G) I.a I.b y)
    (hd : (I.C : ℤ) < deviation G y I.a) :
    Subsolution (operator G) I.a I.b (tightSub G I y) := by
  have hh : (I.delta : ℤ) ≤ deviation G y I.a :=
    (by exact_mod_cast I.delta_bounds.2 : (I.delta : ℤ) ≤ I.C).trans hd.le
  have hle : tightSub G I y ≤ y := by
    intro i
    change max (y i - deviation G y I.a + I.delta) (I.a i) ≤ y i
    exact max_le (by omega) (hy.1.1 i)
  refine ⟨⟨fun i => le_max_right _ _, hle.trans hy.1.2⟩, ?_⟩
  intro i hi
  have he : tightSub G I y i = y i - deviation G y I.a + I.delta := by
    apply max_eq_left
    change I.a i < max (y i - deviation G y I.a + I.delta) (I.a i) at hi
    omega
  have hiy := hy.2 i (hi.trans_le (hle i))
  have hm := (operator_laws G).mono (show shift y (-deviation G y I.a + I.delta) ≤ tightSub G I y by
    intro j
    change y j + (-deviation G y I.a + I.delta) ≤ max (y j - deviation G y I.a + I.delta) (I.a j)
    omega) i
  rw [(operator_laws G).translation] at hm
  dsimp only [shift] at hm
  rw [he]
  omega

theorem tightSuper_solution (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : Supersolution (operator G) I.a I.b z)
    (hd : (I.C : ℤ) < deviation G I.b z) :
    Supersolution (operator G) I.a I.b (tightSuper G I z) := by
  have hh : (I.delta : ℤ) ≤ deviation G I.b z :=
    (by exact_mod_cast I.delta_bounds.2 : (I.delta : ℤ) ≤ I.C).trans hd.le
  have hle : z ≤ tightSuper G I z := by
    intro i
    change z i ≤ min (z i + deviation G I.b z - I.delta) (I.b i)
    exact le_min (by omega) (hz.1.2 i)
  refine ⟨⟨hz.1.1.trans hle, fun i => min_le_right _ _⟩, ?_⟩
  intro i hi
  have he : tightSuper G I z i = z i + deviation G I.b z - I.delta := by
    apply min_eq_left
    change min (z i + deviation G I.b z - I.delta) (I.b i) < I.b i at hi
    omega
  have hiz := hz.2 i ((hle i).trans_lt hi)
  have hm := (operator_laws G).mono (show tightSuper G I z ≤ shift z (deviation G I.b z - I.delta) by
    intro j
    change min (z j + deviation G I.b z - I.delta) (I.b j) ≤ z j + (deviation G I.b z - I.delta)
    omega) i
  rw [(operator_laws G).translation] at hm
  dsimp only [shift] at hm
  rw [he]
  omega

theorem tightSub_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (y : Vec (Fin G.n)) (hd : (I.C : ℤ) < deviation G y I.a) :
    lowerActive I.a (tightSub G I y) ⊆ highCore I y := by
  intro i hi
  have hai := (Finset.mem_filter.mp hi).2
  change I.a i < max (y i - deviation G y I.a + I.delta) (I.a i) at hai
  have hb : (I.width : ℤ) = I.C + I.delta := by
    have h := I.delta_smaller
    unfold SolveBox.C
    omega
  have hdel : 4 * (globalS Bmax : ℤ) * I.delta ≤ I.width := by exact_mod_cast I.delta_bounds.1
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hh : (I.width : ℤ) - 2 * I.delta < y i - I.a i := by omega
  have hm := mul_le_mul_of_nonneg_left hh.le hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by nlinarith only [hm, hdel]⟩

theorem tightSuper_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (z : Vec (Fin G.n)) (hd : (I.C : ℤ) < deviation G I.b z) :
    upperActive I.b (tightSuper G I z) ⊆ lowCore I z := by
  intro i hi
  have hai := (Finset.mem_filter.mp hi).2
  change min (z i + deviation G I.b z - I.delta) (I.b i) < I.b i at hai
  have hb : (I.width : ℤ) = I.C + I.delta := by
    have h := I.delta_smaller
    unfold SolveBox.C
    omega
  have hdel : 4 * (globalS Bmax : ℤ) * I.delta ≤ I.width := by exact_mod_cast I.delta_bounds.1
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hh : (I.width : ℤ) - 2 * I.delta < I.b i - z i := by omega
  have hm := mul_le_mul_of_nonneg_left hh.le hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by nlinarith only [hm, hdel]⟩

theorem tightSub_forces_update (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (y : Vec (Fin G.n)) (r : BoxVector I) (hr : tightSub G I y ≤ r.val) :
    ∃ i, (I.delta : ℤ) ≤ r.val i - I.a i := by
  obtain ⟨i, hi⟩ := deviation_attained G y I.a
  have hh := (le_max_left (y i - deviation G y I.a + I.delta) (I.a i)).trans (hr i)
  exact ⟨i, by omega⟩

theorem tightSuper_forces_update (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (z : Vec (Fin G.n)) (r : BoxVector I) (hr : r.val ≤ tightSuper G I z) :
    ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i := by
  obtain ⟨i, hi⟩ := deviation_attained G I.b z
  have hh : r.val i ≤ z i + deviation G I.b z - I.delta :=
    (hr i).trans (min_le_left (z i + deviation G I.b z - I.delta) (I.b i))
  exact ⟨i, by omega⟩

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem orientationTail_length (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → RandomTree (Orientation P)) (M : ℕ)
    (hm : ∀ q, (child q).All (fun O => O.exceptions.length ≤ M)) :
    (orientationTail G P I qs child).All (fun O => O.exceptions.length ≤ M + 2) := by
  unfold orientationTail
  dsimp only
  split_ifs
  · change 1 ≤ M + 2
    omega
  · change 1 ≤ M + 2
    omega
  · rw [RandomTree.all_bind]
    apply RandomTree.all_of_forall
    intro j
    rw [RandomTree.map, RandomTree.all_bind]
    apply RandomTree.all_mono _ (hm _)
    intro O hO
    change (O.exceptions ++ [_, _]).length ≤ M + 2
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem orient_length (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).All (fun O => O.exceptions.length ≤ 2 * Nat.clog 2 I.width + 1) := by
  by_cases hsmall : I.width ≤ 128 * globalS Bmax
  · rw [orient, dite_eq_left hsmall]
    change (orientBase G P I).exceptions.length ≤ _
    unfold orientBase
    dsimp only
    split_ifs <;> change 1 ≤ _ <;> omega
  · have hB : 128 * globalS Bmax < I.width := Nat.lt_of_not_ge hsmall
    rw [orient, dite_eq_right hsmall]
    dsimp only
    rw [RandomTree.all_bind]
    with_reducible
      refine RandomTree.all_of_forall (centerSteps P hR lower I hB (globalS Bmax) I.midpoint) ?_
    intro qs
    have hr := (I.radius_bounds hB).2.2.2
    have hs := globalS_large Bmax
    have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
    apply RandomTree.all_mono _ (orientationTail_length G P I qs _ (2 * Nat.clog 2 (2 * I.E) + 1)
      (fun q => orient_length G P hR lower (I.wideCentered hB q.val)))
    intro O hO
    omega
termination_by I.width
decreasing_by exact I.E_smaller

theorem flatten_length_bound {α : Type} (ls : List (List α)) (M : ℕ)
    (h : ∀ l ∈ ls, l.length ≤ M) : ls.flatten.length ≤ ls.length * M := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    have hl := h l (List.mem_cons_self ..)
    have ht := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    nlinarith only [hl, ht]

theorem orientPlus_length (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).All
      (fun O => O.exceptions.length ≤ globalListBound G.n Bmax) := by
  rw [orientPlus, RandomTree.map, RandomTree.all_bind]
  have hall := RandomTree.trials_all _ (orient_length G P hR lower I) (globalJ G.n Bmax)
  have hh := RandomTree.all_and _ (RandomTree.trials_length _ _) hall
  apply RandomTree.all_mono _ hh
  intro os hos
  change (os.map Orientation.exceptions).flatten.length ≤ _
  have hf := flatten_length_bound (os.map Orientation.exceptions) (2 * Nat.clog 2 I.width + 1)
    (by
      intro l hl
      obtain ⟨O, hO, rfl⟩ := List.mem_map.mp hl
      exact hos.2 O hO)
  simp only [List.length_map, hos.1] at hf
  have hc := Nat.clog_mono_right 2 (I.bounded.trans (Nat.le_succ Bmax))
  change Nat.clog 2 I.width ≤ Nat.clog 2 (Bmax + 1) at hc
  have hcg : 2 * Nat.clog 2 I.width + 1 ≤ 2 * globalG Bmax + 3 := by unfold globalG; omega
  exact hf.trans (Nat.mul_le_mul_left _ hcg)


open scoped Classical

theorem LowerComparisons.ask_high (G : Game) {Bmax : ℕ} {P : Budgets G.n}
    {lower : LowerSolver (Bmax := Bmax) P} (hl : LowerComparisons G P lower)
    (Q : Budgets G.n) (hQ : parameterRank Q.parameter < parameterRank P.parameter)
    (I : SolveBox G.n Bmax) {y : Vec (Fin G.n)}
    (hy : AdmissibleSub (operator G) I.a I.b y Q) :
    (I.repeated (lower Q hQ I) (globalJ G.n Bmax)).probability (fun p => ¬y ≤ p.val) ≤
      epsilon G.n Bmax :=
  I.repeated_lower _ ((hl Q hQ).1 I y hy) (globalJ_positive _ _)

theorem LowerComparisons.ask_low (G : Game) {Bmax : ℕ} {P : Budgets G.n}
    {lower : LowerSolver (Bmax := Bmax) P} (hl : LowerComparisons G P lower)
    (Q : Budgets G.n) (hQ : parameterRank Q.parameter < parameterRank P.parameter)
    (I : SolveBox G.n Bmax) {z : Vec (Fin G.n)}
    (hz : AdmissibleSuper (operator G) I.a I.b z Q) :
    (I.repeated (lower Q hQ I) (globalJ G.n Bmax)).probability (fun p => ¬p.val ≤ z) ≤
      epsilon G.n Bmax :=
  I.repeated_upper _ ((hl Q hQ).2 I z hz) (globalJ_positive _ _)

theorem tightRequest_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) {y : Vec (Fin G.n)}
    (hy : AdmissibleSub (operator G) I.a I.b y P) :
    (I.repeated (lower P.reduceK (P.reduceK_rank hR) I) (globalJ G.n Bmax)).probability
      (fun r => ¬TightHighRequest G P I y r) ≤ epsilon G.n Bmax := by
  by_cases hd : (I.C : ℤ) < deviation G y I.a
  · by_cases hc : mass P.alpha (highCore I y) ≤ (4 / 5) * P.k
    · have hu : AdmissibleSub (operator G) I.a I.b (tightSub G I y) P.reduceK :=
        ⟨tightSub_solution G I hy.1 hd,
          (mass_mono (fun i => (P.alpha_pos i).le) (tightSub_core G I y hd)).trans hc⟩
      apply le_trans _ (hl.ask_high G P.reduceK (P.reduceK_rank hR) I hu)
      exact RandomTree.probability_mono _ (fun r hf hr => hf (fun _ _ => hr))
    · rw [RandomTree.failure_zero (P := TightHighRequest G P I y) _ (RandomTree.all_of_forall _ (fun _ _ hh => (hc hh).elim))]
      exact epsilon_nonneg _ _
  · rw [RandomTree.failure_zero (P := TightHighRequest G P I y) _ (RandomTree.all_of_forall _ (fun _ hh => (hd hh).elim))]
    exact epsilon_nonneg _ _

theorem tightRequest_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) {z : Vec (Fin G.n)}
    (hz : AdmissibleSuper (operator G) I.a I.b z P) :
    (I.repeated (lower P.reduceM (P.reduceM_rank hR) I) (globalJ G.n Bmax)).probability
      (fun r => ¬TightLowRequest G P I z r) ≤ epsilon G.n Bmax := by
  by_cases hd : (I.C : ℤ) < deviation G I.b z
  · by_cases hc : mass P.beta (lowCore I z) ≤ (4 / 5) * P.m
    · have hu : AdmissibleSuper (operator G) I.a I.b (tightSuper G I z) P.reduceM :=
        ⟨tightSuper_solution G I hz.1 hd,
          (mass_mono (fun i => (P.beta_pos i).le) (tightSuper_core G I z hd)).trans hc⟩
      apply le_trans _ (hl.ask_low G P.reduceM (P.reduceM_rank hR) I hu)
      exact RandomTree.probability_mono _ (fun r hf hr => hf (fun _ _ => hr))
    · rw [RandomTree.failure_zero (P := TightLowRequest G P I z) _ (RandomTree.all_of_forall _ (fun _ _ hh => (hc hh).elim))]
      exact epsilon_nonneg _ _
  · rw [RandomTree.failure_zero (P := TightLowRequest G P I z) _ (RandomTree.all_of_forall _ (fun _ hh => (hd hh).elim))]
    exact epsilon_nonneg _ _

theorem floor_update_volume {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ r.val i - I.a i) :
    volume (I.withFloor r).b (I.withFloor r).a < volume I.b I.a := by
  apply volume_decreases r.property.1 r.property.2
  obtain ⟨i, hi⟩ := h
  have hd := I.delta_positive hB
  intro heq
  have he := congrFun heq i
  omega

theorem ceiling_update_volume {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i) :
    volume (I.withCeiling r).b (I.withCeiling r).a < volume I.b I.a := by
  apply volume_ceiling_decreases r.property.1 r.property.2
  obtain ⟨i, hi⟩ := h
  have hd := I.delta_positive hB
  intro heq
  have he := congrFun heq i
  omega

theorem volume_error_step {v w : ℕ} (h : w < v) {ε : ℚ} (hε : 0 ≤ ε) :
    (2 * (w : ℚ) + 2) * ε ≤ 2 * (v : ℚ) * ε := by
  apply mul_le_mul_of_nonneg_right _ hε
  have hh : (w : ℚ) + 1 ≤ v := by exact_mod_cast h
  linarith only [hh]

theorem tighten_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (y : Vec (Fin G.n)) (hy : AdmissibleSub (operator G) I.a I.b y P) :
    (tighten P hR lower I hB).probability (fun T => ¬TightHigh G P y T) ≤
      (2 * (volume I.b I.a : ℚ) + 2) * epsilon G.n Bmax := by
  rw [tighten]
  have he := epsilon_nonneg G.n Bmax
  have htail : 0 ≤ (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax :=
    mul_nonneg (by positivity) he
  apply le_trans (RandomTree.bind_error _ _ (TightHighRequest G P I y) _
    (ρ := epsilon G.n Bmax) (ε := (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax)
    htail (tightRequest_high G P hR lower hl I hy) ?_) (by ring_nf; rfl)
  intro r₁ hr₁
  dsimp only
  split_ifs with h₁
  · let K := I.withFloor r₁
    let u : Vec (Fin G.n) := fun i => max (y i) (r₁.val i)
    have hu : AdmissibleSub (operator G) K.a K.b u P :=
      hy.raise_floor (operator_laws G) r₁.property.1 r₁.property.2
    have hv := floor_update_volume I hB r₁ h₁
    have hp := tighten_high G P hR lower hl K hB u hu
    have hbound := (volume_error_step hv he).trans
      (show 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax ≤
        (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax by nlinarith only [he])
    apply le_trans _ (hp.trans hbound)
    rw [RandomTree.probability_map]
    apply RandomTree.probability_mono
    intro T hf hg
    obtain ⟨v, huv, hv, hc⟩ := hg
    apply hf
    exact ⟨v, (fun i => (le_max_left _ _).trans (huv i)), hv, hc⟩
  · have hyM : AdmissibleSub (operator G) I.a I.b y P.reduceM := hy
    apply le_trans (RandomTree.bind_error _ _ (fun r₂ : BoxVector I => y ≤ r₂.val) _
      (ρ := epsilon G.n Bmax) (ε := 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he)
      (hl.ask_high G P.reduceM (P.reduceM_rank hR) I hyM) ?_) (by ring_nf; rfl)
    intro r₂ hr₂
    split_ifs with h₂
    · let K := I.withCeiling r₂
      have hu : AdmissibleSub (operator G) K.a K.b y P := hy.restrict_ceiling hr₂
      have hp := tighten_high G P hR lower hl K hB y hu
      apply le_trans _ (hp.trans (volume_error_step (ceiling_update_volume I hB r₂ h₂) he))
      rw [RandomTree.probability_map]
      exact RandomTree.probability_mono _ (fun T hf hg => hf hg)
    · have hok : TightHigh G P y (⟨I, rfl, le_refl _, le_refl _⟩ : InnerBox I) := by
        refine ⟨y, le_refl _, hy, ?_⟩
        intro hd
        by_contra hc
        exact h₁ (tightSub_forces_update G I y r₁ (hr₁ hd (le_of_not_gt hc)))
      rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he
termination_by volume I.b I.a
decreasing_by
  · exact floor_update_volume I hB r₁ h₁
  · exact ceiling_update_volume I hB r₂ h₂

end MeanPayoff

namespace MeanPayoff
open scoped Classical

theorem tighten_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (z : Vec (Fin G.n)) (hz : AdmissibleSuper (operator G) I.a I.b z P) :
    (tighten P hR lower I hB).probability (fun T => ¬TightLow G P z T) ≤
      (2 * (volume I.b I.a : ℚ) + 2) * epsilon G.n Bmax := by
  rw [tighten]
  have he := epsilon_nonneg G.n Bmax
  have htail : 0 ≤ (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax :=
    mul_nonneg (by positivity) he
  have hzK : AdmissibleSuper (operator G) I.a I.b z P.reduceK := hz
  apply le_trans (RandomTree.bind_error _ _ (fun r₁ : BoxVector I => r₁.val ≤ z) _
    (ρ := epsilon G.n Bmax) (ε := (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax)
    htail (hl.ask_low G P.reduceK (P.reduceK_rank hR) I hzK) ?_) (by ring_nf; rfl)
  intro r₁ hr₁
  dsimp only
  split_ifs with h₁
  · let K := I.withFloor r₁
    have hu : AdmissibleSuper (operator G) K.a K.b z P := hz.restrict_floor hr₁
    have hp := tighten_low G P hR lower hl K hB z hu
    have hbound := (volume_error_step (floor_update_volume I hB r₁ h₁) he).trans
      (show 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax ≤
        (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax by nlinarith only [he])
    apply le_trans _ (hp.trans hbound)
    rw [RandomTree.probability_map]
    exact RandomTree.probability_mono _ (fun T hf hg => hf hg)
  · apply le_trans (RandomTree.bind_error _ _ (TightLowRequest G P I z) _
      (ρ := epsilon G.n Bmax) (ε := 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he)
      (tightRequest_low G P hR lower hl I hz) ?_) (by ring_nf; rfl)
    intro r₂ hr₂
    split_ifs with h₂
    · let K := I.withCeiling r₂
      let u : Vec (Fin G.n) := fun i => min (z i) (r₂.val i)
      have hu : AdmissibleSuper (operator G) K.a K.b u P :=
        hz.lower_ceiling (operator_laws G) r₂.property.1 r₂.property.2
      have hp := tighten_low G P hR lower hl K hB u hu
      apply le_trans _ (hp.trans (volume_error_step (ceiling_update_volume I hB r₂ h₂) he))
      rw [RandomTree.probability_map]
      apply RandomTree.probability_mono
      intro T hf hg
      obtain ⟨v, hvu, hv, hc⟩ := hg
      apply hf
      exact ⟨v, (fun i => (hvu i).trans (min_le_left _ _)), hv, hc⟩
    · have hok : TightLow G P z (⟨I, rfl, le_refl _, le_refl _⟩ : InnerBox I) := by
        refine ⟨z, le_refl _, hz, ?_⟩
        intro hd
        by_contra hc
        exact h₂ (tightSuper_forces_update G I z r₂ (hr₂ hd (le_of_not_gt hc)))
      rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he
termination_by volume I.b I.a
decreasing_by
  · exact floor_update_volume I hB r₁ h₁
  · exact ceiling_update_volume I hB r₂ h₂

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Traversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem traverse_relation_error {α β : Type} (f : α → RandomTree β)
    (R : α → β → Prop) (as : List α) {ε : ℚ} (hε : 0 ≤ ε)
    (hf : ∀ a ∈ as, (f a).probability (fun b => ¬R a b) ≤ ε) :
    (traverse f as).probability (fun bs => ¬List.Forall₂ R as bs) ≤ (as.length : ℚ) * ε := by
  classical
  induction as with
  | nil => simp [traverse]
  | cons a as ih =>
    rw [traverse]
    have ht := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
    apply le_trans (bind_error (f a) (fun b => (traverse f as).map (b :: ·))
      (R a) (fun bs => ¬List.Forall₂ R (a :: as) bs)
      (ρ := ε) (ε := (as.length : ℚ) * ε)
      (mul_nonneg (Nat.cast_nonneg _) hε) (hf a (List.mem_cons_self ..)) ?_) ?_
    · intro b hb
      exact map_error (traverse f as) (b :: ·) (List.Forall₂ R as)
        (fun bs => ¬List.Forall₂ R (a :: as) bs) ht
        (fun bs hbs => not_not_intro (List.Forall₂.cons hb hbs))
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring_nf
      rfl

end RandomTree

theorem forall₂_member_left {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) {a : α} (ha : a ∈ as) : ∃ b ∈ bs, R a b := by
  induction h with
  | nil => simp at ha
  | @cons x b as bs hr ht ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self .., hr⟩
    · obtain ⟨c, hc, hr⟩ := ih ha
      exact ⟨c, List.mem_cons_of_mem b hc, hr⟩

theorem forall₂_right_all {α β : Type} {R : α → β → Prop} {Q : β → Prop}
    {as : List α} {bs : List β} (h : List.Forall₂ R as bs)
    (hq : ∀ a b, R a b → Q b) : ∀ b ∈ bs, Q b := by
  induction h with
  | nil => simp
  | @cons a b as bs hr ht ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hq a c hr
    · exact ih c hc

namespace SolveBox

theorem fold_min_lower {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {y : Vec (Fin n)} (hp : y ≤ p.val)
    (hr : ∀ r ∈ rs, y ≤ r.val) : y ≤ (rs.foldl I.minVector p).val := by
  induction rs generalizing p with
  | nil => exact hp
  | cons r rs ih =>
    apply ih (I.minVector p r)
    · intro i
      exact le_min (hp i) (hr r (List.mem_cons_self ..) i)
    · exact fun s hs => hr s (List.mem_cons_of_mem r hs)

theorem fold_max_upper {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {z : Vec (Fin n)} (hp : p.val ≤ z)
    (hr : ∀ r ∈ rs, r.val ≤ z) : (rs.foldl I.maxVector p).val ≤ z := by
  induction rs generalizing p with
  | nil => exact hp
  | cons r rs ih =>
    apply ih (I.maxVector p r)
    · intro i
      exact max_le (hp i) (hr r (List.mem_cons_self ..) i)
    · exact fun s hs => hr s (List.mem_cons_of_mem r hs)

theorem fold_max_seed {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) : p.val ≤ (rs.foldl I.maxVector p).val := by
  induction rs generalizing p with
  | nil => exact le_refl _
  | cons r rs ih =>
    intro i
    exact (le_max_left (p.val i) (r.val i)).trans (ih _ i)

theorem fold_min_seed {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) : (rs.foldl I.minVector p).val ≤ p.val := by
  induction rs generalizing p with
  | nil => exact le_refl _
  | cons r rs ih => exact (ih _).trans (fun i => min_le_left (p.val i) (r.val i))

theorem fold_max_member {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {r : BoxVector I} (hr : r ∈ rs) : r.val ≤ (rs.foldl I.maxVector p).val := by
  induction rs generalizing p with
  | nil => simp at hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · intro i
      exact (le_max_right (p.val i) (r.val i)).trans (I.fold_max_seed rs _ i)
    · exact ih _ hr

theorem fold_min_member {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {r : BoxVector I} (hr : r ∈ rs) : (rs.foldl I.minVector p).val ≤ r.val := by
  induction rs generalizing p with
  | nil => simp at hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (I.fold_min_seed rs _).trans (fun i => min_le_right (p.val i) (r.val i))
    · exact ih _ hr

theorem volume_le {n Bmax : ℕ} (I : SolveBox n Bmax) : volume I.b I.a ≤ n * Bmax := by
  calc
    _ ≤ ∑ _i : Fin n, Bmax := Finset.sum_le_sum (fun i _ => by
      apply (Int.toNat_le).mpr
      exact (I.width_bound i).trans (by exact_mod_cast I.bounded))
    _ = _ := by simp

end SolveBox


theorem RandomTree.imp_error {α : Type} (t : RandomTree α) (Q : Prop) (R : α → Prop)
    {ε : ℚ} (hε : 0 ≤ ε) (h : Q → t.probability (fun a => ¬R a) ≤ ε) :
    t.probability (fun a => ¬(Q → R a)) ≤ ε := by
  classical
  by_cases hQ : Q
  · simpa only [hQ, true_implies] using h hQ
  · have hz : t.All (fun a => Q → R a) := RandomTree.all_of_forall t (fun _ q => (hQ q).elim)
    rw [RandomTree.failure_zero t hz]
    exact hε

theorem finishChoice_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : HighAccuracy G P _ up δ) (hlo : HighAccuracy G P _ lo δ)
    (y : Vec (Fin G.n)) (hy : AdmissibleSub (operator G) I.a I.b y P)
    (ho : (I.C : ℤ) < deviation G y I.a → HighAlternative I P y O) :
    (finishChoice G P hR lower I hB O up lo).probability (fun p : BoxVector I => ¬y ≤ p.val) ≤
      (O.exceptions.length : ℚ) * epsilon G.n Bmax + δ := by
  classical
  have he := epsilon_nonneg G.n Bmax
  unfold finishChoice
  split_ifs with hY
  · let K := I.capHigh I.C I.C_positive (I.C_smaller hB).le
    let u : Vec (Fin G.n) := fun i => max (y i) (K.a i)
    have hua : AdmissibleSub (operator G) K.a K.b u P :=
      hy.raise_floor (operator_laws G) (fun i => le_max_left _ _) K.ordered
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightM H.val) (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    have ht : (RandomTree.traverse f O.exceptions).probability
        (fun rs => ¬List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => y ≤ r.val) O.exceptions rs) ≤
        (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
      apply RandomTree.traverse_relation_error f _ _ he
      intro H _
      exact hl.ask_high G _ _ I hy
    apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
      (List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => y ≤ r.val) O.exceptions)
      (fun p : BoxVector I => ¬y ≤ p.val) hδ ht
    intro rs hrs
    apply RandomTree.map_error up _ (fun p => u ≤ p.val) _ (hup u hua)
    intro p hp hf
    apply hf
    apply I.fold_min_lower
    · exact fun i => (le_max_left (y i) (K.a i)).trans (hp i)
    · exact forall₂_right_all hrs (fun _ _ hr => hr)
  · let K := I.capLow I.C I.C_positive (I.C_smaller hB).le
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightK H.val) (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    by_cases hyK : y ≤ K.b
    · apply le_trans (RandomTree.bind_probability_le (RandomTree.traverse f O.exceptions) _
        (fun p : BoxVector I => ¬y ≤ p.val) (ε := δ) ?_) ?_
      · intro rs
        apply RandomTree.map_error lo _ (fun p => y ≤ p.val) _ (hlo y (hy.restrict_ceiling hyK))
        intro p hp hf
        exact hf (hp.trans (I.fold_max_seed rs _))
      · exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) he)
    · have hd : (I.C : ℤ) < deviation G y I.a := by
        by_contra hn
        apply hyK
        intro i
        change y i ≤ min (I.b i) (I.a i + I.C)
        have hh := le_deviation G y I.a i
        have hb : y i ≤ I.b i := hy.1.1.2 i
        omega
      have hw : ∃ H ∈ O.exceptions, (4 / 5) * P.k < mass P.alpha (lowerActive I.a y ∩ H.val) := by
        rcases ho hd with hy | hw
        · exact (hY hy).elim
        · exact hw
      let R := fun (H : SmallSet P) (r : BoxVector I) =>
        (4 / 5) * P.k < mass P.alpha (lowerActive I.a y ∩ H.val) → y ≤ r.val
      have ht : (RandomTree.traverse f O.exceptions).probability
          (fun rs => ¬List.Forall₂ R O.exceptions rs) ≤
          (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
        apply RandomTree.traverse_relation_error f R _ he
        intro H _
        apply RandomTree.imp_error _ _ _ he
        intro hH
        exact hl.ask_high G _ _ I (reweight_admissible_sub hy hH)
      apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
        (List.Forall₂ R O.exceptions) (fun p : BoxVector I => ¬y ≤ p.val) hδ ht
      intro rs hrs
      obtain ⟨H, hH, hm⟩ := hw
      obtain ⟨r, hr, hRr⟩ := forall₂_member_left hrs hH
      have hok : (lo.map (fun p => rs.foldl I.maxVector
          (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p))).All (fun p => y ≤ p.val) := by
        rw [RandomTree.map, RandomTree.all_bind]
        apply RandomTree.all_of_forall
        intro p
        exact (hRr hm).trans (I.fold_max_member rs _ hr)
      rw [RandomTree.failure_zero _ hok]
      exact hδ



theorem finishChoice_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : LowAccuracy G P _ up δ) (hlo : LowAccuracy G P _ lo δ)
    (z : Vec (Fin G.n)) (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (ho : (I.C : ℤ) < deviation G I.b z → LowAlternative I P z O) :
    (finishChoice G P hR lower I hB O up lo).probability (fun p : BoxVector I => ¬p.val ≤ z) ≤
      (O.exceptions.length : ℚ) * epsilon G.n Bmax + δ := by
  classical
  have he := epsilon_nonneg G.n Bmax
  unfold finishChoice
  split_ifs with hY
  · let K := I.capHigh I.C I.C_positive (I.C_smaller hB).le
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightM H.val) (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    by_cases hzK : K.a ≤ z
    · apply le_trans (RandomTree.bind_probability_le (RandomTree.traverse f O.exceptions) _
        (fun p : BoxVector I => ¬p.val ≤ z) (ε := δ) ?_) ?_
      · intro rs
        apply RandomTree.map_error up _ (fun p => p.val ≤ z) _ (hup z (hz.restrict_floor hzK))
        intro p hp hf
        exact hf ((I.fold_min_seed rs _).trans hp)
      · exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) he)
    · have hd : (I.C : ℤ) < deviation G I.b z := by
        by_contra hn
        apply hzK
        intro i
        change max (I.a i) (I.b i - I.C) ≤ z i
        have hh := le_deviation G I.b z i
        have ha : I.a i ≤ z i := hz.1.1.1 i
        omega
      have hw : ∃ H ∈ O.exceptions, (4 / 5) * P.m < mass P.beta (upperActive I.b z ∩ H.val) := by
        rcases ho hd with hs | hw
        · simp [hY] at hs
        · exact hw
      let R := fun (H : SmallSet P) (r : BoxVector I) =>
        (4 / 5) * P.m < mass P.beta (upperActive I.b z ∩ H.val) → r.val ≤ z
      have ht : (RandomTree.traverse f O.exceptions).probability
          (fun rs => ¬List.Forall₂ R O.exceptions rs) ≤
          (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
        apply RandomTree.traverse_relation_error f R _ he
        intro H _
        apply RandomTree.imp_error _ _ _ he
        intro hH
        exact hl.ask_low G _ _ I (reweight_admissible_super hz hH)
      apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
        (List.Forall₂ R O.exceptions) (fun p : BoxVector I => ¬p.val ≤ z) hδ ht
      intro rs hrs
      obtain ⟨H, hH, hm⟩ := hw
      obtain ⟨r, hr, hRr⟩ := forall₂_member_left hrs hH
      have hok : (up.map (fun p => rs.foldl I.minVector
          (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p))).All (fun p => p.val ≤ z) := by
        rw [RandomTree.map, RandomTree.all_bind]
        apply RandomTree.all_of_forall
        intro p
        exact (I.fold_min_member rs _ hr).trans (hRr hm)
      rw [RandomTree.failure_zero _ hok]
      exact hδ
  · let K := I.capLow I.C I.C_positive (I.C_smaller hB).le
    let u : Vec (Fin G.n) := fun i => min (z i) (K.b i)
    have hua : AdmissibleSuper (operator G) K.a K.b u P :=
      hz.lower_ceiling (operator_laws G) K.ordered (fun i => min_le_left _ _)
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightK H.val) (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    have ht : (RandomTree.traverse f O.exceptions).probability
        (fun rs => ¬List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => r.val ≤ z) O.exceptions rs) ≤
        (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
      apply RandomTree.traverse_relation_error f _ _ he
      intro H _
      exact hl.ask_low G _ _ I hz
    apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
      (List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => r.val ≤ z) O.exceptions)
      (fun p : BoxVector I => ¬p.val ≤ z) hδ ht
    intro rs hrs
    apply RandomTree.map_error lo _ (fun p => p.val ≤ u) _ (hlo u hua)
    intro p hp hf
    apply hf
    apply I.fold_max_upper
    · exact fun i => (hp i).trans (min_le_left (z i) (K.b i))
    · exact forall₂_right_all hrs (fun _ _ hr => hr)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ErrorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem map_bind {α β γ : Type} (t : RandomTree α) (f : α → RandomTree β) (g : β → γ) :
    (t.bind f).map g = t.bind (fun a => (f a).map g) := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simpa only [map, bind] using congrArg₂ coin il ir

theorem failure_and_metadata {α : Type} (t : RandomTree α) (A B : α → Prop) (h : t.All A) :
    t.probability (fun a => ¬(A a ∧ B a)) ≤ t.probability (fun a => ¬B a) := by
  apply probability_mono_all
  exact all_mono t h (fun a ha hf hb => hf ⟨ha, hb⟩)

end RandomTree

theorem nodeError_nonneg (n Bmax : ℕ) : 0 ≤ nodeError n Bmax := by
  unfold nodeError
  exact mul_nonneg (by positivity) (epsilon_nonneg _ _)

theorem orientStage_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : HighAccuracy G P _ up δ) (hlo : HighAccuracy G P _ lo δ)
    (y : Vec (Fin G.n)) (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (I.C : ℤ) < deviation G y I.a → (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    ((orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).bind
      (fun O => finishChoice G P hR lower I hB O up lo)).probability (fun p => ¬y ≤ p.val) ≤
      ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ := by
  let t := orientPlus (orient G P hR lower I) (globalJ G.n Bmax)
  let A := fun O : Orientation P => O.exceptions.length ≤ globalListBound G.n Bmax
  let B := fun O : Orientation P => (I.C : ℤ) < deviation G y I.a → HighAlternative I P y O
  have he := epsilon_nonneg G.n Bmax
  have ht : t.probability (fun O => ¬(A O ∧ B O)) ≤ epsilon G.n Bmax := by
    apply (RandomTree.failure_and_metadata t A B (orientPlus_length G P hR lower I)).trans
    apply RandomTree.imp_error t _ _ he
    intro hd
    exact orientPlus_high G P hR lower hl I y hy (hc hd)
  apply le_trans (RandomTree.bind_error t (fun O => finishChoice G P hR lower I hB O up lo)
    (fun O => A O ∧ B O) (fun p : BoxVector I => ¬y ≤ p.val)
    (ε := (globalListBound G.n Bmax : ℚ) * epsilon G.n Bmax + δ)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) he) hδ) ht ?_) (by ring_nf; rfl)
  intro O hO
  apply (finishChoice_high G P hR lower hl I hB O up lo hδ hup hlo y hy hO.2).trans
  exact add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hO.1) he) le_rfl

theorem orientStage_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : LowAccuracy G P _ up δ) (hlo : LowAccuracy G P _ lo δ)
    (z : Vec (Fin G.n)) (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (I.C : ℤ) < deviation G I.b z → (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    ((orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).bind
      (fun O => finishChoice G P hR lower I hB O up lo)).probability (fun p => ¬p.val ≤ z) ≤
      ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ := by
  let t := orientPlus (orient G P hR lower I) (globalJ G.n Bmax)
  let A := fun O : Orientation P => O.exceptions.length ≤ globalListBound G.n Bmax
  let B := fun O : Orientation P => (I.C : ℤ) < deviation G I.b z → LowAlternative I P z O
  have he := epsilon_nonneg G.n Bmax
  have ht : t.probability (fun O => ¬(A O ∧ B O)) ≤ epsilon G.n Bmax := by
    apply (RandomTree.failure_and_metadata t A B (orientPlus_length G P hR lower I)).trans
    apply RandomTree.imp_error t _ _ he
    intro hd
    exact orientPlus_low G P hR lower hl I z hz (hc hd)
  apply le_trans (RandomTree.bind_error t (fun O => finishChoice G P hR lower I hB O up lo)
    (fun O => A O ∧ B O) (fun p : BoxVector I => ¬p.val ≤ z)
    (ε := (globalListBound G.n Bmax : ℚ) * epsilon G.n Bmax + δ)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) he) hδ) ht ?_) (by ring_nf; rfl)
  intro O hO
  apply (finishChoice_low G P hR lower hl I hB O up lo hδ hup hlo z hz hO.2).trans
  exact add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hO.1) he) le_rfl



theorem node_error_step {n Bmax : ℕ} (I : SolveBox n Bmax) :
    (2 * (volume I.b I.a : ℚ) + 2) * epsilon n Bmax +
      (((globalListBound n Bmax : ℚ) + 1) * epsilon n Bmax +
        ((I.width - 1 : ℕ) : ℚ) * nodeError n Bmax) ≤ (I.width : ℚ) * nodeError n Bmax := by
  have he := epsilon_nonneg n Bmax
  have hv : (volume I.b I.a : ℚ) ≤ (n : ℚ) * Bmax := by exact_mod_cast I.volume_le
  have hp : ((I.width - 1 : ℕ) : ℚ) + 1 = I.width := by
    exact_mod_cast Nat.sub_add_cancel I.positive
  calc
    _ = (2 * (volume I.b I.a : ℚ) + globalListBound n Bmax + 3) * epsilon n Bmax +
        ((I.width - 1 : ℕ) : ℚ) * nodeError n Bmax := by ring
    _ ≤ nodeError n Bmax + ((I.width - 1 : ℕ) : ℚ) * nodeError n Bmax := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (by linarith only [hv]) he
    _ = _ := by rw [← hp]; ring

theorem solveWidth_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P) :
    (solveWidth G P hR lower I).probability (fun p => ¬y ≤ p.val) ≤
      (I.width : ℚ) * nodeError G.n Bmax := by
  by_cases hsmall : I.width ≤ 128 * globalS Bmax
  · have hc : y ≤ (I.exactVector G).val := box_comparison G hy.1 (basic_spec G I.a I.b I.ordered).2.1
    rw [solveWidth, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc)]
    exact mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
  · have hB : 128 * globalS Bmax < I.width := lt_of_not_ge hsmall
    rw [solveWidth, dite_eq_right hsmall]
    dsimp only
    let δ : ℚ := ((I.width - 1 : ℕ) : ℚ) * nodeError G.n Bmax
    have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
    have he := epsilon_nonneg G.n Bmax
    apply le_trans (RandomTree.bind_error (tighten P hR lower I hB) _
      (TightHigh G P y) (fun p : BoxVector I => ¬y ≤ p.val)
      (ε := ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ)
      (add_nonneg (mul_nonneg (by positivity) he) hδ)
      (tighten_high G P hR lower hl I hB y hy) ?_) (node_error_step I)
    intro T hT
    obtain ⟨u, hyu, hu, hcore⟩ := hT
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by change 128 * globalS Bmax < T.box.width; rw [T.width_eq]; exact hB
    let up := solveWidth G P hR lower (K.capHigh K.C K.C_positive (K.C_smaller hK).le)
    let lo := solveWidth G P hR lower (K.capLow K.C K.C_positive (K.C_smaller hK).le)
    have hc : K.C ≤ I.width - 1 := by have hh := K.C_smaller hK; have hw := T.width_eq; dsimp [K] at hh ⊢; omega
    have hup : HighAccuracy G P _ up δ := by
      intro v hv
      apply (solveWidth_high G P hR lower hl (K.capHigh K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    have hlo : HighAccuracy G P _ lo δ := by
      intro v hv
      apply (solveWidth_high G P hR lower hl (K.capLow K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    change ((orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind
      (fun O => (finishChoice G P hR lower K hK O up lo).map T.include)).probability
        (fun p => ¬y ≤ p.val) ≤ _
    rw [← RandomTree.map_bind]
    apply RandomTree.map_error _ T.include (fun p : BoxVector K => u ≤ p.val) _
      (orientStage_high G P hR lower hl K hK up lo hδ hup hlo u hu hcore)
    intro p hp hf
    exact hf (hyu.trans hp)
termination_by I.width
decreasing_by
  all_goals
    change K.C < I.width
    rw [← T.width_eq]
    exact K.C_smaller hK



theorem solveWidth_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P) :
    (solveWidth G P hR lower I).probability (fun p => ¬p.val ≤ z) ≤
      (I.width : ℚ) * nodeError G.n Bmax := by
  by_cases hsmall : I.width ≤ 128 * globalS Bmax
  · have hc : (I.exactVector G).val ≤ z := box_comparison G (basic_spec G I.a I.b I.ordered).1 hz.1
    rw [solveWidth, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc)]
    exact mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
  · have hB : 128 * globalS Bmax < I.width := lt_of_not_ge hsmall
    rw [solveWidth, dite_eq_right hsmall]
    dsimp only
    let δ : ℚ := ((I.width - 1 : ℕ) : ℚ) * nodeError G.n Bmax
    have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
    have he := epsilon_nonneg G.n Bmax
    apply le_trans (RandomTree.bind_error (tighten P hR lower I hB) _
      (TightLow G P z) (fun p : BoxVector I => ¬p.val ≤ z)
      (ε := ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ)
      (add_nonneg (mul_nonneg (by positivity) he) hδ)
      (tighten_low G P hR lower hl I hB z hz) ?_) (node_error_step I)
    intro T hT
    obtain ⟨u, huz, hu, hcore⟩ := hT
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by change 128 * globalS Bmax < T.box.width; rw [T.width_eq]; exact hB
    let up := solveWidth G P hR lower (K.capHigh K.C K.C_positive (K.C_smaller hK).le)
    let lo := solveWidth G P hR lower (K.capLow K.C K.C_positive (K.C_smaller hK).le)
    have hc : K.C ≤ I.width - 1 := by have hh := K.C_smaller hK; have hw := T.width_eq; dsimp [K] at hh ⊢; omega
    have hup : LowAccuracy G P _ up δ := by
      intro v hv
      apply (solveWidth_low G P hR lower hl (K.capHigh K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    have hlo : LowAccuracy G P _ lo δ := by
      intro v hv
      apply (solveWidth_low G P hR lower hl (K.capLow K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    change ((orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind
      (fun O => (finishChoice G P hR lower K hK O up lo).map T.include)).probability
        (fun p => ¬p.val ≤ z) ≤ _
    rw [← RandomTree.map_bind]
    apply RandomTree.map_error _ T.include (fun p : BoxVector K => p.val ≤ u) _
      (orientStage_low G P hR lower hl K hK up lo hδ hup hlo u hu hcore)
    intro p hp hf
    exact hf (hp.trans huz)
termination_by I.width
decreasing_by
  all_goals
    change K.C < I.width
    rw [← T.width_eq]
    exact K.C_smaller hK



theorem root_error_coefficient (n Bmax : ℕ) :
    Bmax * (2 * n * Bmax + globalListBound n Bmax + 3) * 16 ≤ 2 ^ globalJ n Bmax := by
  by_cases hB : Bmax = 0
  · simp [hB]
  have hb : 1 ≤ Bmax := by omega
  let s := globalS Bmax
  let k := s * (n + 1)
  have hs : 16 ≤ s := globalS_large Bmax
  have hsk : s ≤ k := by dsimp [k]; nlinarith
  have hk : 16 ≤ k := hs.trans hsk
  have hn : n ≤ k := by dsimp [k]; nlinarith
  have hg : globalG Bmax ≤ s := by
    have h := globalS_lower Bmax
    change 131072 * (globalG Bmax + 1) ≤ s at h
    omega
  have hclog : Nat.clog 2 (Bmax + 1) ≤ s := by unfold globalG at hg; omega
  have hBs : Bmax ≤ 2 ^ s :=
    (Nat.le_succ Bmax).trans ((Nat.clog_le_iff_le_pow (by norm_num)).mp hclog)
  have hk6 : k ^ 2 ≤ k ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hk7 : k ^ 2 ≤ k ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hJ : globalJ n Bmax ≤ 3 * k ^ 6 := by
    have hpow : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega)
    change 2 * k ^ 6 + 1 ≤ 3 * k ^ 6
    omega
  have hM : globalListBound n Bmax ≤ 9 * k ^ 7 := by
    have hfac : 2 * globalG Bmax + 3 ≤ 3 * k := by omega
    calc
      _ ≤ (3 * k ^ 6) * (3 * k) := Nat.mul_le_mul hJ hfac
      _ = 9 * k ^ 7 := by ring
  have hpoly : 2 * n + globalListBound n Bmax + 3 ≤ 10 * k ^ 7 := by
    have hx : 2 * n + 3 ≤ k ^ 7 := by nlinarith
    omega
  have hpowK : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
  have hten : 10 ≤ 2 ^ (3 * k) := by
    apply le_trans (show 10 ≤ 2 ^ 4 by norm_num)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpolyExp : 10 * k ^ 7 ≤ 2 ^ (10 * k) := by
    calc
      _ ≤ 2 ^ (3 * k) * (2 ^ k) ^ 7 := Nat.mul_le_mul hten (Nat.pow_le_pow_left hpowK 7)
      _ = 2 ^ (10 * k) := by
        rw [← pow_mul, ← pow_add, show 3 * k + k * 7 = 10 * k by omega]
  have hN : Bmax * (2 * n * Bmax + globalListBound n Bmax + 3) ≤ 2 ^ (12 * k) := by
    calc
      _ ≤ Bmax ^ 2 * (2 * n + globalListBound n Bmax + 3) := by
        have hscale : Bmax * (globalListBound n Bmax + 3) ≤
            Bmax ^ 2 * (globalListBound n Bmax + 3) :=
          Nat.mul_le_mul_right _ (by nlinarith : Bmax ≤ Bmax ^ 2)
        nlinarith only [hscale]
      _ ≤ (2 ^ s) ^ 2 * (10 * k ^ 7) := Nat.mul_le_mul (Nat.pow_le_pow_left hBs 2) hpoly
      _ ≤ (2 ^ s) ^ 2 * 2 ^ (10 * k) := Nat.mul_le_mul_left _ hpolyExp
      _ = 2 ^ (s * 2 + 10 * k) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (12 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAbsorb : 12 * k + 4 ≤ globalJ n Bmax := by
    change 12 * k + 4 ≤ 2 * k ^ 6 + 1
    nlinarith
  calc
    _ ≤ 2 ^ (12 * k) * 16 := Nat.mul_le_mul_right 16 hN
    _ = 2 ^ (12 * k + 4) := by rw [pow_add]; rfl
    _ ≤ 2 ^ globalJ n Bmax := Nat.pow_le_pow_right (by norm_num) hAbsorb

theorem root_error_small (n Bmax : ℕ) : (Bmax : ℚ) * nodeError n Bmax ≤ 1 / 16 := by
  have h := root_error_coefficient n Bmax
  have hq : ((Bmax : ℚ) * (2 * n * Bmax + globalListBound n Bmax + 3)) * 16 ≤
      (2 : ℚ) ^ globalJ n Bmax := by exact_mod_cast h
  have hp : 0 < (2 : ℚ) ^ globalJ n Bmax := pow_pos (by norm_num) _
  dsimp [nodeError, epsilon]
  rw [div_pow, one_pow, ← mul_assoc, mul_one_div, div_le_iff₀ hp]
  linarith only [hq]

theorem width_error_small {n Bmax : ℕ} (I : SolveBox n Bmax) :
    (I.width : ℚ) * nodeError n Bmax ≤ 1 / 16 := by
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr I.bounded)
    (nodeError_nonneg _ _)).trans (root_error_small n Bmax)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_CountedTraversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem admissible_bottom {n : ℕ} (P : Budgets n) (F : Vec (Fin n) → Vec (Fin n))
    {a b : Vec (Fin n)} (hab : a ≤ b) : AdmissibleSub F a b a P := by
  refine ⟨⟨⟨le_rfl, hab⟩, fun i hi => (lt_irrefl _ hi).elim⟩, ?_⟩
  simpa [mass, lowerActive] using P.k_pos.le

theorem admissible_top {n : ℕ} (P : Budgets n) (F : Vec (Fin n) → Vec (Fin n))
    {a b : Vec (Fin n)} (hab : a ≤ b) : AdmissibleSuper F a b b P := by
  refine ⟨⟨⟨hab, le_rfl⟩, fun i hi => (lt_irrefl _ hi).elim⟩, ?_⟩
  simpa [mass, upperActive] using P.m_pos.le

theorem solve_comparisons (G : Game) {Bmax : ℕ} (P : Budgets G.n) :
    Comparisons G P (solve G (Bmax := Bmax) P) := by
  classical
  by_cases hR : P.parameter < 1
  · constructor
    · intro I y hy
      have hc := (small_rank_comparisons P hR hy (admissible_top P (operator G) I.ordered)).1
      have hc' : y ≤ (I.smallVector P).val := hc
      rw [solve, dite_eq_left hR, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc')]
      norm_num
    · intro I z hz
      have hc := (small_rank_comparisons P hR (admissible_bottom P (operator G) I.ordered) hz).2
      have hc' : (I.smallVector P).val ≤ z := hc
      rw [solve, dite_eq_left hR, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc')]
      norm_num
  · have hl : LowerComparisons G (Bmax := Bmax) P (fun Q _ K => solve G Q K) := by
      intro Q hQ
      exact solve_comparisons G Q
    constructor
    · intro I y hy
      rw [solve, dite_eq_right hR]
      exact (solveWidth_high G P (le_of_not_gt hR) _ hl I y hy).trans (width_error_small I)
    · intro I z hz
      rw [solve, dite_eq_right hR]
      exact (solveWidth_low G P (le_of_not_gt hR) _ hl I z hz).trans (width_error_small I)
termination_by parameterRank P.parameter



theorem root_sub_admissible (G : Game) {y : Vec (Fin G.n)}
    (hy : Subsolution (operator G) (rootBox G).a (rootBox G).b y) :
    AdmissibleSub (operator G) (rootBox G).a (rootBox G).b y (rootBudgets G) := by
  refine ⟨hy, ?_⟩
  have h := Finset.card_le_card (Finset.subset_univ (lowerActive (rootBox G).a y))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simpa [mass, rootBudgets] using (show ((lowerActive (rootBox G).a y).card : ℚ) ≤ G.n by exact_mod_cast h)

theorem root_super_admissible (G : Game) {z : Vec (Fin G.n)}
    (hz : Supersolution (operator G) (rootBox G).a (rootBox G).b z) :
    AdmissibleSuper (operator G) (rootBox G).a (rootBox G).b z (rootBudgets G) := by
  refine ⟨hz, ?_⟩
  have h := Finset.card_le_card (Finset.subset_univ (upperActive (rootBox G).b z))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simpa [mass, rootBudgets] using (show ((upperActive (rootBox G).b z).card : ℚ) ≤ G.n by exact_mod_cast h)

theorem solve_root_exact (G : Game) :
    (solve G (rootBudgets G) (rootBox G)).probability
      (fun p => p.val ≠ ((rootBox G).exactVector G).val) ≤ 1 / 8 := by
  let I := rootBox G
  let x := (I.exactVector G).val
  have hx := basic_spec G I.a I.b I.ordered
  have h := solve_comparisons G (Bmax := (topWidth G).toNat) (rootBudgets G)
  have hhi := h.1 I x (root_sub_admissible G hx.1)
  have hlo := h.2 I x (root_super_admissible G hx.2.1)
  have hu := RandomTree.probability_union (solve G (rootBudgets G) I)
    (fun p => ¬x ≤ p.val) (fun p => ¬p.val ≤ x)
  have hsub : (solve G (rootBudgets G) I).probability (fun p => p.val ≠ x) ≤
      (solve G (rootBudgets G) I).probability (fun p => ¬x ≤ p.val ∨ ¬p.val ≤ x) := by
    apply RandomTree.probability_mono
    intro p hp
    by_contra han
    have hh := not_or.mp han
    exact hp (le_antisymm (not_not.mp hh.2) (not_not.mp hh.1))
  exact hsub.trans (hu.trans (by linarith only [hhi, hlo]))

theorem gameSolve_failure (G : Game) :
    (gameSolve G).probability (fun out => ¬CorrectSet G out) ≤ 1 / 8 := by
  rw [gameSolve, RandomTree.probability_map]
  apply le_trans (RandomTree.probability_mono _ (fun p hp => ?_)) (solve_root_exact G)
  intro heq
  apply hp
  intro v
  simp only [decide_eq_true_eq]
  rw [heq]
  exact (winning_iff_high G
    ⟨(basic_spec G (rootBox G).a (rootBox G).b (rootBox G).ordered).1,
      (basic_spec G (rootBox G).a (rootBox G).b (rootBox G).ordered).2.1⟩ v).symm

theorem gameSolve_success (G : Game) :
    7 / 8 ≤ (gameSolve G).probability (CorrectSet G) := by
  have h := gameSolve_failure G
  rw [RandomTree.probability_compl] at h
  linarith only [h]


namespace Counted

@[simp] theorem erase_bind {α β : Type} (t : Counted α) (f : α → Counted β) :
    (t.bind f).erase = t.erase.bind (fun a => (f a).erase) := by
  simp [erase, bind, RandomTree.map_bind]

@[simp] theorem erase_trials {α : Type} (t : Counted α) (J : ℕ) :
    (trials t J).erase = RandomTree.trials t.erase J := by
  induction J with
  | zero => rfl
  | succ J ih => simp [trials, RandomTree.trials, ih]

@[simp] theorem erase_traverse {α β : Type} (f : α → Counted β) (as : List α) :
    (traverse f as).erase = RandomTree.traverse (fun a => (f a).erase) as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [traverse, RandomTree.traverse, ih]

end Counted
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_CountedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff


@[simp] theorem SolveBox.erase_repeated {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : Counted (BoxVector I)) (J : ℕ) :
    (I.repeatedCounted t J).erase = I.repeated t.erase J := by
  simp [SolveBox.repeatedCounted, SolveBox.repeated]

namespace CountedAlgorithm

@[simp] theorem erase_centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).erase =
    MeanPayoff.centerUpdate P hR (eraseLower lower) I hB q := by
  simp [centerUpdate, MeanPayoff.centerUpdate, eraseLower]

@[simp] theorem erase_centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).erase =
    MeanPayoff.centerSteps P hR (eraseLower lower) I hB t q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih => simp only [centerSteps, MeanPayoff.centerSteps, Counted.erase_bind,
      erase_centerUpdate, Counted.erase_map, ih]

@[simp] theorem erase_orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → Counted (Orientation P)) :
    (orientationTail G P I qs child).erase =
    MeanPayoff.orientationTail G P I qs (fun q => (child q).erase) := by
  unfold orientationTail MeanPayoff.orientationTail
  dsimp only
  split_ifs <;> simp

@[simp] theorem erase_orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).erase = MeanPayoff.orient G P hR (eraseLower lower) I := by
  rw [orient, MeanPayoff.orient]
  split_ifs with h
  · rfl
  · simp only [Counted.erase_bind, erase_centerSteps, erase_orientationTail]
    apply congrArg (RandomTree.bind _)
    funext qs
    apply congrArg (MeanPayoff.orientationTail G P I qs)
    funext q
    exact erase_orient G P hR lower (I.wideCentered (lt_of_not_ge h) q.val)
termination_by I.width
 decreasing_by exact I.E_smaller

@[simp] theorem erase_orientPlus {n : ℕ} {P : Budgets n}
    (t : Counted (Orientation P)) (J : ℕ) :
    (orientPlus t J).erase = MeanPayoff.orientPlus t.erase J := by
  simp [orientPlus, MeanPayoff.orientPlus]

@[simp] theorem erase_tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).erase = MeanPayoff.tighten P hR (eraseLower lower) I hB := by
  rw [tighten, MeanPayoff.tighten]
  simp only [Counted.erase_bind, SolveBox.erase_repeated]
  congr 1
  funext r₁
  split_ifs with h₁
  · simp only [Counted.erase_map, erase_tighten P hR lower (I.withFloor r₁) hB]
  · simp only [Counted.erase_bind, SolveBox.erase_repeated]
    congr 1
    funext r₂
    split_ifs with h₂
    · simp only [Counted.erase_map, erase_tighten P hR lower (I.withCeiling r₂) hB]
    · rfl
termination_by volume I.b I.a
 decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

@[simp] theorem erase_finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    (finishChoice G P hR lower I hB O up lo).erase =
    MeanPayoff.finishChoice G P hR (eraseLower lower) I hB O up.erase lo.erase := by
  unfold finishChoice MeanPayoff.finishChoice
  split_ifs <;> simp [eraseLower]

@[simp] theorem erase_solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).erase = MeanPayoff.solveWidth G P hR (eraseLower lower) I := by
  rw [solveWidth, MeanPayoff.solveWidth, Counted.erase_charge]
  split_ifs with hB
  · rfl
  · simp only [Counted.erase_bind, erase_tighten]
    congr 1
    funext T
    simp only [erase_orientPlus, erase_orient]
    congr 1
    funext O
    simp only [Counted.erase_map, erase_finishChoice]
    congr 2
    · exact erase_solveWidth G P hR lower _
    · exact erase_solveWidth G P hR lower _
termination_by I.width
 decreasing_by
  all_goals
    change T.box.C < I.width
    rw [← T.width_eq]
    exact T.box.C_smaller (by rw [T.width_eq]; omega)

@[simp] theorem erase_solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (solve G P I).erase = MeanPayoff.solve G P I := by
  rw [solve, MeanPayoff.solve]
  split_ifs with hR
  · rfl
  · rw [erase_solveWidth]
    congr 1
    funext Q h K
    exact erase_solve G Q K
termination_by parameterRank P.parameter

end CountedAlgorithm
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BitDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree
open scoped Classical

theorem prefix_sum {α : Type} (t : RandomTree α) (f : α → ℚ) (T : ℕ)
    (hT : t.bitDepth ≤ T) :
    ∑ bits : Fin T → Bool, f (t.readPrefix bits) = (2 : ℚ) ^ T * t.expect f := by
  induction T generalizing t with
  | zero =>
    cases t with
    | leaf a => simp [expect]
    | coin l r => simp [bitDepth] at hT
  | succ T ih =>
    cases t with
    | leaf a => simp [expect]
    | coin l r =>
      have hl : l.bitDepth ≤ T := by simp only [bitDepth] at hT; omega
      have hr : r.bitDepth ≤ T := by simp only [bitDepth] at hT; omega
      have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (T + 1) => Bool))
        (fun bits => f ((coin l r).readPrefix bits))
      rw [← he, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, readPrefix_coin_cons]
      rw [Fintype.sum_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih l hl, ih r hr]
      simp only [expect, pow_succ]
      ring

theorem prefix_probability {α : Type} (t : RandomTree α) (P : α → Prop) (T : ℕ)
    (hT : t.bitDepth ≤ T) :
    ((Finset.univ.filter (fun bits : Fin T → Bool => P (t.readPrefix bits))).card : ℚ) =
      (2 : ℚ) ^ T * t.probability P := by
  classical
  have h := prefix_sum t (fun a => if P a then (1 : ℚ) else 0) T hT
  simpa only [probability, Finset.sum_boole] using h

end RandomTree
end MeanPayoff

namespace MeanPayoff

theorem clog_real_le_twice_logb (L : ℕ) :
    (Nat.clog 2 (L + 2) : ℝ) ≤ 2 * Real.logb 2 (L + 2) := by
  have hpos : (0 : ℝ) < L + 2 := by positivity
  have hlog : (1 : ℝ) ≤ Real.logb 2 (L + 2) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).mpr
    simp only [Real.rpow_one]
    linarith only [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  have hceil := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.logb 2 (L + 2))
  have he : ⌈Real.logb 2 (L + 2)⌉₊ = Nat.clog 2 (L + 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (L + 2)
  rw [he] at hceil
  linarith only [hceil, hlog]


namespace RandomTree

theorem Path.all {α : Type} {t : RandomTree α} {a : α} {d : ℕ}
    (h : Path t a d) {P : α → Prop} (hp : t.All P) : P a := by
  induction h with
  | leaf a => exact hp
  | left h ih => exact ih hp.1
  | right h ih => exact ih hp.2

theorem Path.depth_le {α : Type} {t : RandomTree α} {a : α} {d : ℕ}
    (h : Path t a d) : d ≤ t.bitDepth := by
  induction h with
  | leaf a => exact le_rfl
  | left h ih => dsimp [bitDepth]; omega
  | right h ih => dsimp [bitDepth]; omega

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Online
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem consume_path {α : Type} (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    pos ≤ (t.consume bits pos).2 ∧
      Path t (t.consume bits pos).1 ((t.consume bits pos).2 - pos) := by
  induction t generalizing pos with
  | leaf a => exact ⟨le_rfl, by simp only [consume, Nat.sub_self]; exact .leaf a⟩
  | coin l r il ir =>
    simp only [consume]
    split
    · obtain ⟨hp, hh⟩ := ir (pos + 1)
      exact ⟨by omega, by convert Path.right (l := l) hh using 1 ; omega⟩
    · obtain ⟨hp, hh⟩ := il (pos + 1)
      exact ⟨by omega, by convert Path.left (r := r) hh using 1 ; omega⟩

theorem consume_read {α : Type} (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    (t.consume bits pos).1 = t.read (fun k => bits (pos + k)) := by
  induction t generalizing pos with
  | leaf a => rfl
  | coin l r il ir =>
    simp only [consume, read, Nat.add_zero]
    split
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ir (pos + 1)
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using il (pos + 1)

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace TwoPhase

theorem pad_even {t : ℕ} (bits : Fin (2 * t) → Bool) :
    (fun j => padBits bits (2 * j)) = padBits (even bits) := by
  funext j
  by_cases hj : j < t
  · simp only [padBits, show 2 * j < 2 * t by omega, hj, ↓reduceDIte, even]
  · simp only [padBits, show ¬2 * j < 2 * t by omega, hj, ↓reduceDIte]

open scoped Classical

theorem successful_count (t : ℕ) (Q : (Fin t → Bool) → Prop) :
    (Finset.univ.filter (fun bits : Fin (2 * t) → Bool => Q (even bits))).card =
      2 ^ t * (Finset.univ.filter Q).card := by
  have h := Equiv.sum_comp (equiv t) (fun bits => if Q (even bits) then (1 : ℕ) else 0)
  rw [Fintype.sum_prod_type] at h
  simp only [equiv, Equiv.coe_fn_mk, even_interleave] at h
  calc
    _ = ∑ x : Fin t → Bool, if Q x then 2 ^ t else 0 := by
      simpa [Finset.sum_boole, Fintype.card_fun] using h.symm
    _ = _ := by simp [Finset.sum_ite, Nat.mul_comm]

end TwoPhase
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace BinaryStack

theorem cells_push (xs : List Bool) (b : Bool) (h : ℤ) :
    cells (b :: xs) (h - 1) = Function.update (cells xs h) (h - 1) (some b) := by
  funext j
  by_cases he : j = h - 1
  · subst j; simp [cells]
  · rw [Function.update_of_ne he]
    by_cases hj : h ≤ j
    · have hn : (j - (h - 1)).toNat = (j - h).toNat + 1 := by omega
      simp only [cells, show 0 ≤ j - (h - 1) by omega, show 0 ≤ j - h by omega,
        ↓reduceIte, hn, List.getElem?_cons_succ]
    · have hn : j < h - 1 := by omega
      simp only [cells, show ¬0 ≤ j - (h - 1) by omega, show ¬0 ≤ j - h by omega, ↓reduceIte]

theorem cells_pop (xs : List Bool) (b : Bool) (h : ℤ) :
    cells xs (h + 1) = Function.update (cells (b :: xs) h) h none := by
  funext j
  by_cases he : j = h
  · subst j; simp [cells]
  · rw [Function.update_of_ne he]
    by_cases hj : h < j
    · have hn : (j - h).toNat = (j - (h + 1)).toNat + 1 := by omega
      simp only [cells, show 0 ≤ j - (h + 1) by omega, show 0 ≤ j - h by omega,
        ↓reduceIte, hn, List.getElem?_cons_succ]
    · simp only [cells, show ¬0 ≤ j - (h + 1) by omega, show ¬0 ≤ j - h by omega, ↓reduceIte]

theorem cells_emit (xs : List Bool) (b : Bool) :
    cells (xs ++ [b]) 0 = Function.update (cells xs 0) (xs.length : ℤ) (some b) := by
  funext j
  by_cases he : j = xs.length
  · subst j; simp [cells]
  · rw [Function.update_of_ne he]
    by_cases hj : 0 ≤ j
    · simp only [cells, sub_zero, hj, ↓reduceIte]
      by_cases hk : j.toNat < xs.length
      · rw [List.getElem?_append_left hk]
      · have hg : xs.length < j.toNat := by omega
        simp only [List.getElem?_eq_none (by omega : xs.length ≤ j.toNat),
          List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega :
            (xs ++ [b]).length ≤ j.toNat)]
    · simp only [cells, sub_zero, hj, ↓reduceIte]

theorem cells_applyOp (op : Op) (xs : List Bool) (h : ℤ) :
    let h' := h + (shiftOp op xs).offset
    let t := Function.update (cells xs h) h (firstWrite op xs.head?)
    Function.update t h' ((pendingWrite op).or (t h')) =
      cells (applyOp op xs) h' := by
  cases op with
  | keep => simp [shiftOp, Direction.offset, firstWrite, pendingWrite, applyOp]
  | pop =>
    cases xs with
    | nil => simp [shiftOp, Direction.offset, firstWrite, pendingWrite, applyOp]
    | cons b xs =>
      simp only [shiftOp, Direction.offset, firstWrite, pendingWrite, Option.none_or,
        Function.update_eq_self, applyOp, List.tail_cons]
      exact (cells_pop xs b h).symm
  | push b =>
    simp only [shiftOp, Direction.offset, firstWrite, pendingWrite,
      ← cells_top xs h, Function.update_eq_self, Option.some_or, applyOp]
    simpa only [sub_eq_add_neg] using (cells_push xs b h).symm

theorem double_step (P : Program) (c : Config P) (h : Fin 2 → ℤ) (b₁ b₂ : Bool) :
    ∃ h', MeanPayoff.step (machine P)
      (MeanPayoff.step (machine P) (concrete P c h) b₁) b₂ =
        concrete P (step P c b₁) h' := by
  rcases c with ⟨q, xs, out⟩
  cases q with
  | none => exact ⟨h, rfl⟩
  | some q =>
    let top : Fin 2 → Option Bool := fun k => (xs k).head?
    cases ha : P.transition q top b₁ with
    | none =>
      refine ⟨h, ?_⟩
      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal]
      have ht : (fun k : Fin 2 =>
          (if hk : k.val < 2 then cells (xs ⟨k.val, hk⟩) (h ⟨k.val, hk⟩)
            else cells out 0)
          (if hk : k.val < 2 then h ⟨k.val, hk⟩ else out.length)) = top := by
        funext k
        simp only [Fin.isLt, ↓reduceDIte, Fin.eta, cells_top, top]
      simp only [ht, ha, Option.map_none]
      simp only [top] at ha
      simp only [step]
      rw [ha]
      rfl
    | some a =>
      refine ⟨newHeads ⟨some q, xs, out⟩ h a, ?_⟩

      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal]
      have ht : (fun k : Fin 2 =>
          (if hk : k.val < 2 then cells (xs ⟨k.val, hk⟩) (h ⟨k.val, hk⟩)
            else cells out 0)
          (if hk : k.val < 2 then h ⟨k.val, hk⟩ else out.length)) = top := by
        funext k
        simp only [Fin.isLt, ↓reduceDIte, Fin.eta, cells_top, top]
      simp only [ht, ha, Option.map_some, decode_pending]
      simp only [top] at ha
      simp only [step]
      rw [ha]
      apply concrete_ext
      · rfl
      · funext k
        fin_cases k
        · simp [newHeads, Direction.offset]
        · simp [newHeads, Direction.offset]
        · cases he : a.emit <;> simp [Direction.offset, he]
      · funext k
        fin_cases k
        · simpa [newHeads] using cells_applyOp (a.work 0) (xs 0) (h 0)
        · simpa [newHeads] using cells_applyOp (a.work 1) (xs 1) (h 1)
        · cases he : a.emit with
          | none =>
            have hu : Function.update (cells out 0) (out.length : ℤ) none = cells out 0 := by
              simpa only [cells_end] using Function.update_eq_self (out.length : ℤ) (cells out 0)
            simp [he, hu]
          | some b => simpa [newHeads, he] using (cells_emit out b).symm

theorem concrete_initial (P : Program) (code : List Bool) :
    MeanPayoff.initial (machine P) code = concrete P (initial P code) (fun _ => 0) := by
  apply concrete_ext
  · rfl
  · funext k; fin_cases k <;> rfl
  · funext k j
    fin_cases k
    · simp [MeanPayoff.initial, concrete, initial, cells]
    · simp [MeanPayoff.initial, concrete, initial, cells]
    · simp [MeanPayoff.initial, concrete, initial]

theorem simulate (P : Program) (code : List Bool) (bits : ℕ → Bool) (t : ℕ) :
    ∃ h, MeanPayoff.run (machine P) code bits (2 * t) =
      concrete P (run P code (fun j => bits (2 * j)) t) h := by
  induction t with
  | zero => exact ⟨fun _ => 0, concrete_initial P code⟩
  | succ t ih =>
    obtain ⟨h, hh⟩ := ih
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, MeanPayoff.run, MeanPayoff.run, hh]
    obtain ⟨h', he⟩ := double_step P (run P code (fun j => bits (2 * j)) t) h
      (bits (2 * t)) (bits (2 * t + 1))
    exact ⟨h', he⟩

theorem cells_outside (xs : List Bool) (j : ℤ)
    (hj : j < 0 ∨ (xs.length : ℤ) ≤ j) : cells xs 0 j = none := by
  rcases hj with hj | hj
  · simp [cells, show ¬0 ≤ j by omega]
  · simp [cells, show 0 ≤ j by omega, List.getElem?_eq_none (by omega : xs.length ≤ j.toNat)]

end BinaryStack
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_SignedBits
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff
namespace SignedBits
open BinaryStack.Addition (value low carry full_adder)

theorem value_bound (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true, List.length_cons, pow_succ] <;> omega

theorem val_negative (w : Word) : w.val < 0 ↔ w.sign = true := by
  cases w with
  | mk s xs =>
    have h : (value xs : ℤ) < 2 ^ xs.length := by exact_mod_cast value_bound xs
    cases s <;> simp [Word.val] ; omega

end SignedBits
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Packets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

theorem correctList_packet (G : Game) (M : Machine) (c : Configuration M) (out : List Bool)
    (h : BinaryInput.CorrectList G out) (hh : c.control = none)
    (ht : c.tape 2 = BinaryStack.cells out 0) : CorrectOutput G c := by
  refine ⟨hh, ?_, ?_, ?_⟩
  · intro v
    rw [ht]
    simpa only [BinaryStack.cells, sub_zero, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast] using h.2 v
  · intro v
    have hv : v.val < out.length := by rw [h.1]; exact v.isLt
    have he : out[v.val]? = some out[v.val] := List.getElem?_eq_getElem hv
    have hc := h.2 v
    rw [he, Option.some.injEq] at hc
    rw [ht]
    simp only [BinaryStack.cells, sub_zero, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, he, Option.some.injEq, ← hc]
    cases out[v.val] <;> simp
  · intro j hj
    rw [ht]
    apply BinaryStack.cells_outside
    simpa only [h.1] using hj

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Instructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits

theorem advance_front {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (n : ℕ) :
    advance P bits c (n + 1) = advance P (fun j => bits (j + 1)) (step P c (bits 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step P (advance P bits c (n + 1)) (bits (n + 1)) = _
    rw [ih]; rfl

namespace Compile

theorem clock_pos {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) : 1 ≤ clock P c coin :=
  (step_simulation_all P c coin).choose_spec.1

theorem clock_bound {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) :
    clock P c coin ≤ 4 * storeSize c.stack + 2 * K + 6 :=
  (step_simulation_all P c coin).choose_spec.2.1

theorem clock_simulation {K : ℕ} (P : Program K) (c : Config P) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (embed P c) (clock P c (bits 0)) =
      embed P (RegisterBits.step P c (bits 0)) :=
  (step_simulation_all P c (bits 0)).choose_spec.2.2 bits rfl

end Compile


namespace Compile
open BinaryStack (advance applyOp)

theorem encode_escape (xs : List Bool) : encode xs = escape xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, escape, ih]

theorem encode_initial {K : ℕ} (P : Program K) (input : List Bool) :
    encodeAll (List.ofFn (RegisterBits.initial P input).stack) =
      escape input ++ List.replicate K false := by
  cases K with
  | zero => exact Fin.elim0 (P.read P.start)
  | succ K =>
    have he : (fun j : Fin K => (RegisterBits.initial P input).stack j.succ) = fun _ => [] := by
      funext j; simp [RegisterBits.initial]
    rw [List.ofFn_succ, he]
    simp [RegisterBits.initial, encodeAll, encode_escape, List.replicate_succ,
      List.append_assoc, List.ofFn_const]

theorem init_move_all {K : ℕ} (P : Program K) (xs ys out : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (cfg P .initMove xs ys out) xs.length =
      cfg P .initMove [] (xs.reverse ++ ys) out := by
  induction xs generalizing ys bits with
  | nil => simp [BinaryStack.advance]
  | cons b xs ih =>
    rw [List.length_cons, BinaryStack.advance_front, init_move_step, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem init_pad_all {K : ℕ} (P : Program K) (n : ℕ) (hn : n < K + 1)
    (xs ys out : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (cfg P (.initPad ⟨n, hn⟩) xs ys out) (n + 1) =
      cfg P .initRestore (List.replicate n false ++ xs) ys out := by
  induction n generalizing xs bits with
  | zero => simp [BinaryStack.advance]
  | succ n ih =>
    rw [BinaryStack.advance_front, init_pad_succ, ih]
    rw [List.replicate_succ', List.append_assoc]
    rfl

theorem init_restore_all {K : ℕ} (P : Program K) (xs ys out : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (cfg P .initRestore xs ys out) (2 * ys.length + 1) =
      cfg P (.source P.start) (escape ys.reverse ++ xs) [] out := by
  induction ys generalizing xs bits with
  | nil => simp [BinaryStack.advance, escape]
  | cons b ys ih =>
    rw [List.length_cons, show 2 * (ys.length + 1) + 1 = (2 * ys.length + 1 + 1) + 1 by omega,
      BinaryStack.advance_front, init_restore_step, BinaryStack.advance_front, init_tag_step, ih]
    simp [List.reverse_cons, escape, List.append_assoc]

theorem initial_cfg {K : ℕ} (P : Program K) (input : List Bool) :
    BinaryStack.initial (program P) input = cfg P .initMove input [] [] := by
  apply BinaryStack.Config.ext
  · rfl
  · funext i; fin_cases i <;> simp [BinaryStack.initial, cfg]
  · rfl

theorem initialize_correct {K : ℕ} (P : Program K) (input : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (BinaryStack.initial (program P) input)
        (3 * input.length + K + 3) = embed P (RegisterBits.initial P input) := by
  rw [initial_cfg]
  have hn : 3 * input.length + K + 3 = (input.length + 1) + (K + 1) + (2 * input.length + 1) := by omega
  rw [hn, advance_add (a := input.length + 1 + (K + 1)) (b := 2 * input.length + 1),
    advance_add (a := input.length + 1) (b := K + 1)]
  have hm : BinaryStack.advance (program P) bits (cfg P .initMove input [] []) (input.length + 1) =
      cfg P (.initPad ⟨K, by omega⟩) [] input.reverse [] := by
    change BinaryStack.step (program P)
      (BinaryStack.advance (program P) bits (cfg P .initMove input [] []) input.length) (bits input.length) = _
    rw [init_move_all, List.append_nil, init_move_empty]
  rw [hm, init_pad_all, List.append_nil]
  rw [show 2 * input.length + 1 = 2 * input.reverse.length + 1 by simp, init_restore_all]
  simp only [List.reverse_reverse]
  unfold embed
  rw [encode_initial]
  rfl

end Compile
end MeanPayoff.RegisterBits
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits
open RandomTree

namespace Compile

theorem schedule_expect {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (f : Config P → ℚ) :
    (schedule P n c).expect f = (tree P n c).expect f := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [schedule, tree, expect, expect_wait, ih]

theorem schedule_all {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (Q : Config P → Prop) :
    (schedule P n c).All Q ↔ (tree P n c).All Q := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [schedule, tree, All, all_wait, ih]

theorem schedule_depth {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) :
    (schedule P n c).bitDepth ≤ overhead K (storeSize c.stack) n := by
  induction n generalizing c with
  | zero => simp [schedule, bitDepth, overhead]
  | succ n ih =>
    have hbranch (b : Bool) :
        clock P c b - 1 + (schedule P n (step P c b)).bitDepth + 1 ≤
          overhead K (storeSize c.stack) (n + 1) := by
      have hs := step_size P c b
      have hi := ih (step P c b)
      have ht := clock_bound P c b
      have hp := clock_pos P c b
      have hm := Nat.mul_le_mul_left (4 * n) hs
      have he : clock P c b - 1 + 1 = clock P c b := by omega
      unfold overhead at *
      nlinarith only [hi, ht, he, hm]
    simp only [schedule, bitDepth, depth_wait]
    have h₀ := hbranch false
    have h₁ := hbranch true
    omega

theorem consume_schedule_step {K : ℕ} (P : Program K) (n : ℕ) (c : Config P)
    (bits : ℕ → Bool) (pos : ℕ) :
    (schedule P (n + 1) c).consume bits pos =
      (schedule P n (step P c (bits pos))).consume bits (pos + clock P c (bits pos)) := by
  have ht := clock_pos P c (bits pos)
  simp only [schedule, consume, consume_wait]
  cases hb : bits pos <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at * <;>
    congr 1 <;> omega

theorem consume_simulation {K : ℕ} (P : Program K) (n : ℕ) (c : Config P)
    (bits : ℕ → Bool) (pos : ℕ) :
    let r := (schedule P n c).consume bits pos
    BinaryStack.advance (program P) (fun j => bits (pos + j)) (embed P c) (r.2 - pos) = embed P r.1 := by
  induction n generalizing c pos with
  | zero => simp [schedule, consume, BinaryStack.advance]
  | succ n ih =>
    simp only [consume_schedule_step]
    let a := clock P c (bits pos)
    let d := step P c (bits pos)
    let r := (schedule P n d).consume bits (pos + a)
    have hr : pos + a ≤ r.2 := (consume_path (schedule P n d) bits (pos + a)).1
    have hi := ih d (pos + a)
    change BinaryStack.advance (program P) (fun j => bits (pos + j)) (embed P c) (r.2 - pos) = _
    rw [show r.2 - pos = a + (r.2 - (pos + a)) by omega, advance_add]
    have hc := clock_simulation P c (fun j => bits (pos + j))
    simp only [Nat.add_zero] at hc
    rw [hc]
    simpa only [Nat.add_assoc] using hi

theorem initialized_depth {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) :
    (initializedTree P input n).bitDepth ≤
      3 * input.length + K + 3 + overhead K (storeSize (initial P input).stack) n := by
  rw [initializedTree, depth_wait]
  exact Nat.add_le_add_left (schedule_depth P n _) _

theorem initialized_simulation {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (bits : ℕ → Bool) :
    let r := (initializedTree P input n).consume bits 0
    BinaryStack.run (program P) input bits r.2 = embed P r.1 := by
  simp only [initializedTree, consume_wait, Nat.zero_add]
  let a := 3 * input.length + K + 3
  let r := (schedule P n (initial P input)).consume bits a
  have hr : a ≤ r.2 := (consume_path (schedule P n (initial P input)) bits a).1
  rw [← BinaryStack.advance_initial]
  change BinaryStack.advance (program P) bits (BinaryStack.initial (program P) input) r.2 = _
  rw [show r.2 = a + (r.2 - a) by omega, advance_add, initialize_correct]
  exact consume_simulation P n (initial P input) bits a

end Compile
end MeanPayoff.RegisterBits

namespace MeanPayoff.BinaryStack

theorem run_after_halt (P : Program) (input : List Bool) (bits : ℕ → Bool) (a b : ℕ)
    (ha : (run P input bits a).control = none) (hab : a ≤ b) :
    run P input bits b = run P input bits a := by
  rw [← advance_initial, show b = a + (b - a) by omega,
    RegisterBits.Compile.advance_add, advance_initial, advance_halted P _ _ ha]

end MeanPayoff.BinaryStack
namespace MeanPayoff.RegisterBits.Compile
open RandomTree

theorem embed_halted {K : ℕ} (P : Program K) (c : Config P) (hc : c.control = none) :
    (embed P c).control = none := by simp [embed, sourceCfg, hc]; rfl

theorem initialized_all {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) (Q : Config P → Prop) :
    (initializedTree P input n).All Q ↔ (tree P n (initial P input)).All Q := by
  simp only [initializedTree, all_wait, schedule_all]

theorem initialized_expect {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) (f : Config P → ℚ) :
    (initializedTree P input n).expect f = (tree P n (initial P input)).expect f := by
  simp only [initializedTree, expect_wait, schedule_expect]

theorem padded_run {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (hh : (tree P n (initial P input)).All (fun c => c.control = none))
    (bits : ℕ → Bool) :
    BinaryStack.run (program P) input bits (bound P input n) =
      embed P ((initializedTree P input n).read bits) := by
  let t := initializedTree P input n
  let r := t.consume bits 0
  have hp : Path t r.1 r.2 := by simpa only [Nat.sub_zero] using (consume_path t bits 0).2
  have hr : r.2 ≤ bound P input n := hp.depth_le.trans (initialized_depth P input n)
  have ha : r.1.control = none := hp.all ((initialized_all P input n _).2 hh)
  have hs : BinaryStack.run (program P) input bits r.2 = embed P r.1 := initialized_simulation P input n bits
  have halted : (BinaryStack.run (program P) input bits r.2).control = none := by
    rw [hs]; exact embed_halted P r.1 ha
  rw [BinaryStack.run_after_halt _ _ _ r.2 _ halted hr, hs]
  have he : r.1 = t.read bits := by simpa only [Nat.zero_add] using consume_read t bits 0
  rw [he]

theorem machine_packet {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (hh : (tree P n (initial P input)).All (fun c => c.control = none))
    (bits : Fin (2 * bound P input n) → Bool) :
    let out := ((initializedTree P input n).readPrefix (TwoPhase.even bits)).output
    let c := MeanPayoff.run (machine P) input (padBits bits) (2 * bound P input n)
    c.control = none ∧ c.tape 2 = BinaryStack.cells out 0 := by
  obtain ⟨h, he⟩ := BinaryStack.simulate (program P) input (padBits bits) (bound P input n)
  dsimp only [machine]
  rw [he, TwoPhase.pad_even, padded_run P input n hh]
  let c := (initializedTree P input n).read (padBits (TwoPhase.even bits))
  have hc : c.control = none := by
    have hp := (consume_path (initializedTree P input n) (padBits (TwoPhase.even bits)) 0).2
    have ha := hp.all ((initialized_all P input n _).2 hh)
    simpa only [consume_read, Nat.zero_add] using ha
  constructor
  · exact (BinaryStack.concrete_halted _ _ _).2 (embed_halted P c hc)
  · rfl

open scoped Classical

theorem machine_probability {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (hh : (tree P n (initial P input)).All (fun c => c.control = none))
    (Q : List Bool → Prop) :
    ((Finset.univ.filter (fun bits : Fin (2 * bound P input n) → Bool =>
      ∃ out, Q out ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * bound P input n)).control = none ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * bound P input n)).tape 2 =
          BinaryStack.cells out 0)).card : ℚ) ≥
      (2 : ℚ) ^ (2 * bound P input n) *
        (tree P n (initial P input)).probability (fun c => Q c.output) := by
  let T := bound P input n
  let t := initializedTree P input n
  have ht : t.bitDepth ≤ T := initialized_depth P input n
  have hprob : t.probability (fun c => Q c.output) =
      (tree P n (initial P input)).probability (fun c => Q c.output) :=
    initialized_expect P input n _
  have hc := prefix_probability t (fun c => Q c.output) T ht
  rw [hprob] at hc
  have he := TwoPhase.successful_count T (fun bits => Q (t.readPrefix bits).output)
  have hsub : (Finset.univ.filter (fun bits : Fin (2 * T) → Bool =>
      Q (t.readPrefix (TwoPhase.even bits)).output)).card ≤
      (Finset.univ.filter (fun bits : Fin (2 * T) → Bool =>
      ∃ out, Q out ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * T)).control = none ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * T)).tape 2 =
          BinaryStack.cells out 0)).card := by
    apply Finset.card_le_card
    intro bits hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨_, hb, machine_packet P input n hh bits⟩
  rw [he] at hsub
  have hcast : ((2 ^ T * (Finset.univ.filter (fun bits : Fin T → Bool => Q (t.readPrefix bits).output)).card : ℕ) : ℚ) ≤ _ :=
    (Nat.cast_le (α := ℚ)).2 hsub
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
  rw [hc] at hcast
  convert hcast using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 2 * T = T + T by omega, pow_add]; ring

end MeanPayoff.RegisterBits.Compile
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Stack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace Counted
@[simp] theorem map_bind {α β γ : Type} (t : Counted α) (f : α → Counted β) (g : β → γ) :
    (t.bind f).map g = t.bind (fun a => (f a).map g) := by
  ext; simp [map, bind, RandomTree.map_bind]
@[simp] theorem bind_assoc {α β γ : Type} (t : Counted α) (f : α → Counted β) (g : β → Counted γ) :
    (t.bind f).bind g = t.bind (fun a => (f a).bind g) := by
  ext; simp [bind, RandomTree.map_bind, Nat.add_assoc]
@[simp] theorem charge_bind {α β : Type} (t : Counted α) (c : ℕ) (f : α → Counted β) :
    (t.charge c).bind f = (t.bind f).charge c := by
  ext; simp [charge, bind, RandomTree.map_bind, Nat.add_assoc]
end Counted

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_TreeDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits
open BinaryData.Take (advance_add)

theorem step_coinFree {K : ℕ} (P : Program K) (h : CoinFree P) (c : Config P) (b : Bool) :
    step P c b = step P c false := by
  cases hc : c.control with
  | none => simp [step,hc]
  | some q => simp only [step,hc]; rw [h q _ b]

theorem advance_coinFree {K : ℕ} (P : Program K) (h : CoinFree P) (c : Config P)
    (bits : ℕ → Bool) (n : ℕ) : advance P bits c n = advance P (fun _ => false) c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance,ih,step_coinFree P h]

end MeanPayoff.RegisterBits

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sorting
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Halve
open BinaryData

theorem halve_val (w : SignedBits.Word) : (halve w).val = w.val / 2 := by
  have hv := SignedBits.val_uncons w.sign w.digits
  change w.val = (SignedBits.head w.sign w.digits).toNat +
    2*(SignedBits.Word.mk w.sign w.digits.tail).val at hv
  have hb : (SignedBits.head w.sign w.digits).toNat ≤ 1 := by
    cases (SignedBits.head w.sign w.digits) <;> decide
  change (SignedBits.Word.mk w.sign w.digits.tail).val = _
  omega

end MeanPayoff.TreeDevice.Halve
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData
open Code

namespace Word
@[simp] theorem half_val (x : W) : (half x).val=x.val/2 := Halve.halve_val _
@[simp] theorem average_val (x y : W) : (average (x,y)).val=(x.val+y.val)/2 := by simp [average]
end Word
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedArithmetic
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingParsed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Word

theorem addFold_val (a : W) (xs : List W) :
    (addFold (a,xs)).val=a.val+(xs.map SignedBits.Word.val).sum := by
  change (Fold.fold add.eval a xs).val=_
  induction xs generalizing a with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    change (Fold.fold add.eval (add (a,x)) xs).val=_
    have h := ih (add (a,x))
    simp only [List.map_cons,List.sum_cons] at *
    rw [add_val] at h
    omega
@[simp] theorem sum_val (xs : List W) : (sum xs).val=(xs.map SignedBits.Word.val).sum := by
  change (addFold (Median.zeroWord,xs)).val=_
  rw [addFold_val]
  change 0+_=_
  omega

end Word

namespace Counter
@[simp] theorem word_val (xs : Count) : (word xs).val=xs.length := by
  simp [word,Code.const,List.sum_replicate]
end Counter
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_InputCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace NaturalLog

theorem recurrence (n : ℕ) (h : 0<n) : Nat.clog 2 (n+1)=Nat.clog 2 (n/2+1)+1 := by
  rw [Nat.clog_of_one_lt (by decide : 1<2) (by omega : 1<n+1)]
  congr 2
  omega

theorem fold_stopped (w : W) (hw : w.val ≤ 0) (c xs : Count) :
    Fold.fold step.eval (w,c) xs = (w,c) := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    change Fold.fold step.eval (step ((w,c),u)) us = _
    rw [step_eval]
    dsimp only
    rw [ite_eq_right (by omega)]
    exact ih

theorem fold_length (w : W) (hw : 0 ≤ w.val) (c xs : Count) (hf : w.digits.length ≤ xs.length) :
    (Fold.fold step.eval (w,c) xs).2.length = c.length+Nat.clog 2 (w.val.toNat+1) := by
  induction xs generalizing w c with
  | nil =>
    have hd : w.digits=[] := List.length_eq_zero_iff.mp (by simpa using hf)
    have hs : w.sign=false := Bool.eq_false_iff.mpr (fun h => (not_lt_of_ge hw) ((SignedBits.val_negative w).mpr h))
    have hz : w.val=0 := by simp [SignedBits.Word.val,hd,hs,BinaryStack.Addition.value]
    simp [Fold.fold,hz]
  | cons u us ih =>
    by_cases hp : 0<w.val
    · have hd : w.digits ≠ [] := by
        intro hd
        have hb : w.val ≤ 0 := by
          cases hs : w.sign <;> simp [SignedBits.Word.val,hd,hs,BinaryStack.Addition.value]
        omega
      have hw' : 0 ≤ (Word.half w).val := by rw [Word.half_val]; omega
      have hf' : (Word.half w).digits.length ≤ us.length := by
        rw [Word.half_length]
        have : 0<w.digits.length := by simpa only [List.length_pos_iff] using hd
        simp only [List.length_cons] at hf
        omega
      change (Fold.fold step.eval (step ((w,c),u)) us).2.length = _
      rw [step_eval,ite_eq_left hp,ih (Word.half w) hw' (()::c) hf',List.length_cons]
      have hn : 0<w.val.toNat := by omega
      have he : (Word.half w).val.toNat=w.val.toNat/2 := by rw [Word.half_val]; omega
      rw [he,recurrence _ hn]
      omega
    · have hz : w.val=0 := by omega
      rw [fold_stopped w (by omega)]
      simp [hz]

theorem length_exact (w : W) (hw : 0 ≤ w.val) : (length w).length=Nat.clog 2 (w.val.toNat+1) := by
  change (Fold.fold step.eval (w,[]) (Word.digitCount w)).2.length=_
  simpa only [List.length_nil,Nat.zero_add] using fold_length w hw [] (Word.digitCount w) (by rw [Word.digitCount_length])

theorem ceil_exact (w : W) (hw : 0 < w.val) : (ceil w).length=Nat.clog 2 w.val.toNat := by
  change (length (Word.sub (w,Word.constant 1 w))).length=_
  rw [length_exact _ (by simp; omega)]
  congr 1
  simp only [Word.sub_val,Word.constant_val]
  omega
end NaturalLog
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Allocation
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Allocation

 theorem fold_length (a cs : Count) : (Fold.fold double.eval a cs).length=2^cs.length*a.length := by
  induction cs generalizing a with
  | nil => simp [Fold.fold]
  | cons u us ih =>
    change (Fold.fold double.eval (double (a,u)) us).length=_
    rw [ih]
    simp only [double,comp_eval,pair_eval,fst_eval,Counter.add_length,List.length_cons,pow_succ]
    ring

 theorem fold_bound : ∃ K d : ℕ, ∀ (a cs : Count),
    (Fold.device double.device).limit (a,cs) ≤ K*(a.length*2^cs.length+cs.length+1)^d := by
  obtain ⟨K,d,h⟩ := double.polynomial
  refine ⟨49+K*8^d,d+2,?_⟩
  intro a cs
  let N := a.length*2^cs.length+cs.length+1
  have hn : 1≤N := by dsimp [N]; omega
  have ha : ∀ k ≤ cs.length, treeSize (encode (Fold.fold double.eval a (cs.take k))) ≤ 3*N := by
    intro k hk
    rw [Size.count,fold_length]
    have hp : 2^(cs.take k).length ≤ 2^cs.length := Nat.pow_le_pow_right (by decide) ((List.length_take_le _ _).trans hk)
    have hm := Nat.mul_le_mul_right a.length hp
    have hm' : 2^(cs.take k).length*a.length ≤ a.length*2^cs.length := by simpa only [Nat.mul_comm] using hm
    dsimp [N]; omega
  have hs : treeSize (encode cs)≤3*N := by rw [Size.count]; dsimp [N]; omega
  have ht := Fold.time_of_prefix_bound double.device K d (3*N) (3*N) h a cs hs ha
  have hb : 3*N+3*N+2≤8*N := by omega

  have hd : cs.length+1≤N := by dsimp [N]; omega
  change Fold.time double.device a cs+2 ≤ _
  have hbpow := Nat.mul_le_mul_left K (Nat.pow_le_pow_left hb d)
  have hlow : 12*(3*N)+K*(3*N+3*N+2)^d+11 ≤ 47*N+K*(8*N)^d := by omega
  have ht' := ht.trans (Nat.mul_le_mul hd hlow)
  have hnp : N≤N^(d+1) := Nat.le_pow (by omega)
  have hp : N^d ≤ N^(d+1) := Nat.pow_le_pow_right hn (by omega)
  have hpow : N^2≤N^(d+2) := Nat.pow_le_pow_right hn (by omega)
  rw [mul_pow] at ht'

  have hx : N*(47*N+K*8^d*N^d)+2 ≤ (49+K*8^d)*N^(d+2) := by
    have h1 := Nat.mul_le_mul_left 47 hpow
    have h2 : N*N^d≤N^(d+2) := by rw [←pow_succ']; exact Nat.pow_le_pow_right hn (by omega)
    have h3 := Nat.mul_le_mul_left (K*8^d) h2
    have h4 : 1≤N^(d+2) := one_le_pow₀ hn
    nlinarith
  exact (Nat.add_le_add_right ht' 2).trans (by simpa only [Nat.mul_assoc] using hx)
end Allocation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff

namespace PolyBound
variable {ι : Type} {r f g : ι→ℕ}
theorem mono (h : PolyBound r g) (hf : ∀ i, f i≤g i) : PolyBound r f := by
  obtain ⟨K,d,h⟩ := h
  exact ⟨K,d,fun i => (hf i).trans (h i)⟩
theorem base (r : ι→ℕ) : PolyBound r r := ⟨1,1,by intro i; simp⟩
theorem const (r : ι→ℕ) (a : ℕ) : PolyBound r (fun _ => a) := ⟨a,0,by simp⟩
theorem add (hf : PolyBound r f) (hg : PolyBound r g) : PolyBound r (fun i => f i+g i) := by
  obtain ⟨K,d,hf⟩ := hf
  obtain ⟨M,e,hg⟩ := hg
  refine ⟨K+M,d+e,fun i => ?_⟩
  have hp : 1 ≤ r i+1 := by omega
  have hd := (hf i).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hp (show d≤d+e by omega)))
  have he := (hg i).trans (Nat.mul_le_mul_left M (Nat.pow_le_pow_right hp (show e≤d+e by omega)))
  nlinarith
theorem mul (hf : PolyBound r f) (hg : PolyBound r g) : PolyBound r (fun i => f i*g i) := by
  obtain ⟨K,d,hf⟩ := hf
  obtain ⟨M,e,hg⟩ := hg
  refine ⟨K*M,d+e,fun i => ?_⟩
  have h := Nat.mul_le_mul (hf i) (hg i)
  rw [pow_add]
  nlinarith only [h]
theorem pow (hf : PolyBound r f) (n : ℕ) : PolyBound r (fun i => f i^n) := by
  obtain ⟨K,d,hf⟩ := hf
  refine ⟨K^n,d*n,fun i => ?_⟩
  simpa only [mul_pow,←pow_mul] using Nat.pow_le_pow_left (hf i) n
end PolyBound
namespace TreeDevice
open BinaryData
 theorem polynomial_limit {ι α β : Type} {ea : α→Data} {eb : β→Data} {f : α→β}
    {F : Device ea eb f} (hF : PolynomialCost F) (r : ι→ℕ) (x : ι→α)
    (hx : PolyBound r (fun i => treeSize (ea (x i)))) : PolyBound r (fun i => F.limit (x i)) := by
  obtain ⟨K,d,h⟩ := hF
  exact ((PolyBound.const r K).mul ((hx.add (PolyBound.const r 1)).pow d)).mono (fun i => h (x i))
 theorem polynomial_output {ι α β : Type} {ea : α→Data} {eb : β→Data} {f : α→β}
    (F : Device ea eb f) (r : ι→ℕ) (x : ι→α)
    (hx : PolyBound r (fun i => treeSize (ea (x i))))
    (hc : PolyBound r (fun i => F.limit (x i))) : PolyBound r (fun i => treeSize (eb (f (x i)))) :=
  (hx.add hc).mono (fun i => output_size F (x i))
end TreeDevice
end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Realizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Box5
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (config_ext)
 theorem injective : Function.Injective place := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)
 theorem installs (a b c : List Bool) :
    install place (core [] [] []) ![a,b,c]=core a b c := by
  funext i; fin_cases i
  · exact install_at place injective _ _ 0
  · exact install_at place injective _ _ 1
  · exact install_at place injective _ _ 2
  · exact install_off place _ _ _ (by intro j; fin_cases j <;> decide)
  · exact install_off place _ _ _ (by intro j; fin_cases j <;> decide)
 theorem quiet : CoinFree program := by intro q top b; rfl
 theorem runs (bs out : List Bool) (bits : ℕ→Bool) :
    advance program bits ⟨some program.start,core bs [] [],out⟩
      (2*bs.length+2+feedCost bs+1)=⟨none,core [] (encode (listData bs)) [],out⟩ := by
  have h := rename_advance Box.program place injective (core [] [] [])
    (Box.cfg .reverse bs [] [] out) bits (2*bs.length+2+feedCost bs+1)
  rw [Box.boxes] at h
  change advance (rename Box.program place) bits
    ⟨some (Box.enc .reverse),core bs [] [],out⟩ _=_
  simp only [renamed,Box.cfg,Box.stopped,installs,List.append_nil] at h
  convert h using 1; rfl
end MeanPayoff.Box5

end

section
namespace MeanPayoff.Emit
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
 theorem quiet : CoinFree program := by intro q top b; rfl
 theorem nil_run (xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (false::xs) out) 2=⟨none,core xs [] [],out⟩ := by
  apply config_ext <;> (try rfl)
  · funext i; fin_cases i <;> rfl
  · change out++[]=out
    exact List.append_nil out
 theorem one (b : Bool) (xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (consCode b++xs) out) (if b then 4 else 2)=cfg 0 xs (out++[b]) := by
  cases b <;> apply config_ext <;> (try rfl)
  all_goals first
  | (funext i; fin_cases i <;> rfl)
  | simp [advance,RegisterBits.step,cfg,program,core,consCode,BinaryStack.applyOp]
 theorem runs (bs xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (encode (listData bs)++xs) out) (cost bs)=
      ⟨none,core xs [] [],out++bs⟩ := by
  induction bs generalizing out bits with
  | nil => simpa only [cost,List.map_nil,List.sum_nil,Nat.zero_add,List.append_nil,encode_list_nil,List.singleton_append] using nil_run xs out bits
  | cons b bs ih =>
    have hc : cost (b::bs)=(if b then 4 else 2)+cost bs := by simp only [cost,List.map_cons,List.sum_cons]; omega
    rw [hc,encode_list_cons,List.append_assoc,advance_add,one,ih]
    simp only [List.append_assoc,List.singleton_append]
 theorem bound (bs : List Bool) : cost bs≤4*bs.length+2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hc : cost (b::bs)=(if b then 4 else 2)+cost bs := by simp only [cost,List.map_cons,List.sum_cons]; omega
    rw [hc,List.length_cons]
    split <;> omega
end MeanPayoff.Emit

end

section
namespace MeanPayoff.RegisterBits.Sequence5
open BinaryData.Take (advance_add)
variable (P Q : Program 5)
 theorem quiet (hP : CoinFree P) (hQ : CoinFree Q) : CoinFree (program P Q) :=
  Flow.compile_coinFree _ (by intro p; fin_cases p; exact hP; exact hQ) (by intros; rfl)
 theorem finish_output (F : Flow.Program 5) (p : Fin F.nodes)
    (s t : Fin 5→List Bool) (out result : List Bool) (bits : ℕ→Bool) (N : ℕ)
    (h : advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,result⟩)
    (hn : ∀ top b, F.next p top b=none) :
    ∃ n≤N+1, advance (Flow.compile F) bits (Flow.state F p s out) n=⟨none,t,result⟩ := by
  obtain ⟨n,hn',hh⟩ := Flow.macro_runs F p s out bits N (by rw [h])
  rw [h] at hh
  refine ⟨n+1,by omega,?_⟩
  simp only [advance,hh,Flow.step_boundary,hn]
 theorem runs (s t u : Fin 5→List Bool) (out result : List Bool) (N M : ℕ)
    (hP : ∀ bits, advance P bits ⟨some P.start,s,out⟩ N=⟨none,t,out⟩)
    (hQ : ∀ bits, advance Q bits ⟨some Q.start,t,out⟩ M=⟨none,u,result⟩)
    (bits : ℕ→Bool) : advance (program P Q) bits ⟨some (program P Q).start,s,out⟩ (N+M+2)=⟨none,u,result⟩ := by
  obtain ⟨a,ha,ea⟩ := Flow.hop (flow P Q) (0 : Fin 2) (1 : Fin 2) s t out bits N (hP bits) (by intros; rfl)
  obtain ⟨b,hb,eb⟩ := finish_output (flow P Q) (1 : Fin 2) t u out result (fun j => bits (a+j)) M (hQ _) (by intros; rfl)
  apply advance_pad _ _ _ bits (n:=a+b) (by omega) ?_ rfl
  change advance _ bits (Flow.state (flow P Q) (0 : Fin 2) s out) (a+b)=_
  rw [advance_add,ea,eb]
  rfl
end MeanPayoff.RegisterBits.Sequence5

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Preparation
 theorem logarithm_length (d : Digits) : (logarithm d).length=Nat.clog 2 (d.bits.length+2) := by
  change (NaturalLog.ceil (Counter.word (Counter.inc (Counter.inc (inputLength d))))).length=_
  rw [NaturalLog.ceil_exact _ (by rw [Counter.word_val]; simp only [Counter.inc_length]; positivity),Counter.word_val,Int.toNat_natCast]
  change Nat.clog 2 ((d.bits.map (fun _ => ())).length+1+1)=_
  simp only [List.length_map,Nat.add_assoc]
 theorem exponent_length (d : Digits) : (exponent d).length=25000*(Nat.clog 2 (d.bits.length+2))^2 := by
  simp only [exponent,comp_eval,pair_eval,Counter.mul_length,const_eval,List.length_replicate,Counter.fixedPower_length,logarithm_length]
end Preparation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified.Preparation
open BinaryData
 theorem seed_eval (d : Digits) : seed d=(exponent d,root d) := rfl
 theorem inflate_limit (z : Count×Seed) : inflate.limit z=Allocation.device.limit z.1+1+
    24*treeSize (encode (Fold.fold Allocation.double.eval [()] z.1))+24*treeSize (encode z.2)+50 := by
  rcases z with ⟨c,s⟩
  rw [inflate,pairMap_limit]
  change _+1+24*_+12*_+12*_+50=_
  simp only [id_eq]
  omega
 theorem device_limit (d : Digits) : device.limit d=
    seed.device.limit d+inflate.limit (seed d)+
      assemble.device.limit (Fold.fold Allocation.double.eval [()] (exponent d),root d)+4 := by
  simp only [device, compose_limit]
  simp only [seed_eval]
  omega
end MeanPayoff.TreeDevice.Certified.Preparation

end

section
namespace MeanPayoff.TreeDevice.Certified.Preparation
open BinaryData
 theorem exponent_poly : PolynomialCost exponent.device := exponent.polynomial
 theorem root_poly : PolynomialCost root.device := root.polynomial
 theorem seed_poly : PolynomialCost seed.device := PolynomialCost.fanout exponent_poly root_poly
 theorem assemble_poly : PolynomialCost assemble.device := assemble.polynomial
end MeanPayoff.TreeDevice.Certified.Preparation

end

section
namespace MeanPayoff.TreeDevice.Certified.Preparation
open BinaryData
 theorem input_bound : PolyBound resource (fun d => treeSize (encode d)) :=
  (PolyBound.base resource).mono (fun _ => Nat.le_add_right _ _)
 theorem seed_cost : PolyBound resource seed.device.limit := by
  obtain ⟨K,e,h⟩ := seed_poly
  refine ⟨K,e,fun d => (h d).trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.le_add_right _ _) 1
 theorem seed_size_le (d : Digits) : treeSize (encode (seed d)) ≤ treeSize (encode d)+seed.device.limit d :=
  output_size seed.device d
 theorem seed_size : PolyBound resource (fun d => treeSize (encode (seed d))) :=
  (input_bound.add seed_cost).mono seed_size_le
 theorem exponent_size : PolyBound resource (fun d => treeSize (encode (exponent d))) := by
  apply seed_size.mono
  intro d
  have h := Size.fst (seed d)
  rw [seed_eval] at h
  exact h
 theorem exponent_size_length : PolyBound resource (fun d => (exponent d).length) :=
  exponent_size.mono (fun _ => Size.length _)
 theorem power_bound : PolyBound resource (fun d => 2^(exponent d).length) :=
  (PolyBound.base resource).mono (fun _ => Nat.le_add_left _ _)
 theorem allocation_init_cost : PolyBound resource (fun d => Allocation.init.device.limit (exponent d)) :=
  polynomial_limit Allocation.init.polynomial resource exponent exponent_size
 theorem allocation_fold_cost : PolyBound resource
    (fun d => (Fold.device Allocation.double.device).limit ([()],exponent d)) := by
  obtain ⟨K,e,hK⟩ := Allocation.fold_bound
  apply ((PolyBound.const resource K).mul
    (((power_bound.add exponent_size_length).add (PolyBound.const resource 1)).pow e)).mono
  intro d
  simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul,Nat.add_comm] using hK [()] (exponent d)
 theorem allocation_cost : PolyBound resource (fun d => Allocation.device.limit (exponent d)) := by
  apply ((allocation_init_cost.add allocation_fold_cost).add (PolyBound.const resource 2)).mono
  intro d
  rfl
 theorem allocation_size : PolyBound resource
    (fun d => treeSize (encode (Fold.fold Allocation.double.eval [()] (exponent d)))) :=
  polynomial_output Allocation.device resource exponent exponent_size allocation_cost
 theorem root_size : PolyBound resource (fun d => treeSize (encode (root d))) := by
  apply seed_size.mono
  intro d
  have h := Size.snd (seed d)
  rw [seed_eval] at h
  exact h
 theorem inflate_cost : PolyBound resource (fun d => inflate.limit (seed d)) := by
  apply ((((allocation_cost.add (PolyBound.const resource 1)).add
    ((PolyBound.const resource 24).mul allocation_size)).add
    ((PolyBound.const resource 24).mul root_size)).add (PolyBound.const resource 50)).mono
  intro d
  rw [inflate_limit,seed_eval]
 theorem inflate_size : PolyBound resource
    (fun d => treeSize (encode (Fold.fold Allocation.double.eval [()] (exponent d),root d))) := by
  have h := polynomial_output inflate resource (fun d => seed d) seed_size inflate_cost
  simpa only [seed_eval] using h
 theorem assemble_cost : PolyBound resource
    (fun d => assemble.device.limit (Fold.fold Allocation.double.eval [()] (exponent d),root d)) :=
  @polynomial_limit Digits (Count×Seed) (Count×Aux) encode encode assemble.eval assemble.device
    assemble_poly resource (fun d => (Fold.fold Allocation.double.eval [()] (exponent d),root d)) inflate_size
 theorem cost_bound : PolyBound resource device.limit := by
  apply (((seed_cost.add inflate_cost).add assemble_cost).add (PolyBound.const resource 4)).mono
  intro d
  rw [device_limit]
 theorem output_size_le (d : Digits) : treeSize (encode (value d)) ≤ treeSize (encode d)+device.limit d :=
  output_size device d
 theorem output_bound : PolyBound resource (fun d => treeSize (encode (value d))) :=
  (input_bound.add cost_bound).mono output_size_le
end MeanPayoff.TreeDevice.Certified.Preparation

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Traces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits
open RandomTree BinaryData.Take

namespace Traces
variable {K : ℕ} {P : Program K} {c d : Config P} {t : RandomTree (Config P)}
 theorem leaf (c : Config P) : Traces P c (.leaf c) := by intro bits pos; simp [consume,advance]
 theorem wait (n : ℕ) (h : ∀ bits, advance P bits c n=d) (ht : Traces P d t) :
    Traces P c (RandomTree.wait n t) := by
  intro bits pos
  simp only [consume_wait]
  have hp := (consume_path t bits (pos+n)).1
  rw [show (t.consume bits (pos+n)).2-pos=n+((t.consume bits (pos+n)).2-(pos+n)) by omega,
    advance_add,h]
  simpa only [Nat.add_assoc] using ht bits (pos+n)
 theorem coin {l r : RandomTree (Config P)}
    (hl : Traces P (step P c false) l) (hr : Traces P (step P c true) r) :
    Traces P c (.coin l r) := by
  intro bits pos
  simp only [consume]
  split
  next hb =>
    have hp := (consume_path r bits (pos+1)).1
    rw [show (r.consume bits (pos+1)).2-pos=((r.consume bits (pos+1)).2-(pos+1))+1 by omega,
      advance_front]
    simp only [Nat.add_zero,hb]
    convert hr bits (pos+1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext j
    congr 1
    omega
  next hb =>
    have hp := (consume_path l bits (pos+1)).1
    have he : bits pos=false := Bool.eq_false_iff.mpr hb
    rw [show (l.consume bits (pos+1)).2-pos=((l.consume bits (pos+1)).2-(pos+1))+1 by omega,
      advance_front]
    simp only [Nat.add_zero,he]
    convert hl bits (pos+1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext j
    congr 1
    omega
 theorem padded (ht : Traces P c t) (hh : t.All (fun s => s.control=none))
    {N : ℕ} (hN : t.bitDepth≤N) (bits : ℕ→Bool) : advance P bits c N=t.read bits := by
  have hp := (consume_path t bits 0).2
  have hr : (t.consume bits 0).2≤N := by simpa only [Nat.sub_zero] using hp.depth_le.trans hN
  have hs := ht bits 0
  simp only [Nat.zero_add,Nat.sub_zero] at hs
  have hn := hp.all hh
  have ha := advance_pad P c (t.consume bits 0).1 bits hr hs hn
  simpa only [consume_read,Nat.zero_add] using ha
end Traces
 theorem read_tree {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (bits : ℕ→Bool) :
    (tree P n c).read bits=advance P bits c n := by
  induction n generalizing c bits with
  | zero => rfl
  | succ n ih =>
    rw [advance_front]
    simp only [tree,RandomTree.read]
    split <;> simp_all only
 theorem Traces.tree_all {K : ℕ} {P : Program K} {c : Config P} {t : RandomTree (Config P)}
    (ht : Traces P c t) (hh : t.All (fun s => s.control=none)) {N : ℕ} (hN : t.bitDepth≤N) :
    (tree P N c).All (fun s => s.control=none) := by
  apply all_of_read
  intro bits
  rw [read_tree,ht.padded hh hN]
  have h := ((consume_path t bits 0).2).all hh
  simpa only [consume_read,Nat.zero_add] using h

 theorem Flow.quiet_runs {K : ℕ} (F : Flow.Program K) (p : Fin F.nodes)
    (hq : CoinFree (F.block p)) (s t : Fin K→List Bool) (out out' : List Bool) (N : ℕ)
    (h : ∀ bits, advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,out'⟩) :
    ∃ d≤N, ∀ bits, advance (Flow.compile F) bits (Flow.state F p s out) d=Flow.edge F p t out' := by
  let c : Config (F.block p) := ⟨some (F.block p).start,s,out⟩
  obtain ⟨d,hd,hh,hn,he⟩ := first_termination (F.block p) c (fun _ => false) N (by rw [h])
  refine ⟨d,hd,?_⟩
  intro bits
  have hn' : ∀ j<d, (advance (F.block p) bits c j).control≠none := by
    intro j hj
    rw [advance_coinFree _ hq]
    exact hn j hj
  change advance _ bits (Flow.embed F p c) d=_
  rw [Flow.advance_inner F p c bits d hn',advance_coinFree _ hq,he,h]
  rfl
end MeanPayoff.RegisterBits

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_RandomTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits.Flow
open BinaryData.Take
 theorem quiet_hop_all {K : ℕ} (F : Program K) (p : Fin F.nodes)
    (hq : CoinFree (F.block p)) (s t : Fin K→List Bool) (out out' : List Bool) (N : ℕ)
    (h : ∀ bits, advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,out'⟩)
    (d : Config (compile F)) (he : ∀ b, RegisterBits.step (compile F) (edge F p t out') b=d) :
    ∃ n≤N+1, ∀ bits, advance (compile F) bits (state F p s out) n=d := by
  obtain ⟨n,hn,hh⟩ := quiet_runs F p hq s t out out' N h
  exact ⟨n+1,by omega,fun bits => by rw [advance,hh,he]⟩
 theorem skip_edge (F : Program 5) (p : Fin F.nodes) (hp : F.block p=TreeDevice.skip)
    (s : Fin 5→List Bool) (out : List Bool) (b : Bool) :
    RegisterBits.step (compile F) (state F p s out) b=edge F p s out := by
  have h := step_inner F p ⟨some (F.block p).start,s,out⟩ (by simp) b
  change RegisterBits.step _ (state F p s out) b=_ at h
  rw [h]
  have ht : ∀ q top b, (F.block p).transition q top b=none := by
    rw [hp]; intros; rfl
  simp only [RegisterBits.step,ht]
  rfl
end MeanPayoff.RegisterBits.Flow
namespace MeanPayoff.RandomTable
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
variable (pre post : RegisterBits.Program 5)
 theorem skip_step (p : Fin 12) (h0 : p≠0) (h9 : p≠9) (h11 : p≠11)
    (xs ys out : List Bool) (b : Bool) :
    RegisterBits.step (program pre post) (cfg pre post p xs ys out) b=edge pre post p xs ys out := by
  exact Flow.skip_edge (flow pre post) p (by simp [flow,h0,h9,h11]) _ _ _
 theorem boundary (p : Fin 12) (xs ys out : List Bool) (b : Bool) :
    RegisterBits.step (program pre post) (edge pre post p xs ys out) b =
    match (flow pre post).next p ((core xs ys []) ((flow pre post).read p)).head? b with
    | none => ⟨none,core xs ys [],out⟩
    | some a => Flow.state (flow pre post) a.next
        (Function.update (core xs ys []) ((flow pre post).read p)
          (BinaryStack.applyOp a.work ((core xs ys []) ((flow pre post).read p)))) (out++a.emit.toList) :=
  by
    convert Flow.step_boundary (flow pre post) p (core xs ys []) out b using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    cases (flow pre post).next p ((core xs ys []) ((flow pre post).read p)).head? b <;> rfl
 theorem wait_two (p q : Fin 12) (h0 : p≠0) (h9 : p≠9) (h11 : p≠11)
    (xs ys xs' ys' out : List Bool)
    (h : ∀ b, RegisterBits.step (program pre post) (edge pre post p xs ys out) b=cfg pre post q xs' ys' out)
    (bits : ℕ→Bool) : advance (program pre post) bits (cfg pre post p xs ys out) 2=cfg pre post q xs' ys' out := by
  simp only [advance,skip_step pre post p h0 h9 h11,h]
 theorem loop_one (ns xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 3 (true::false::ns++xs) ys out) 5 =
      edge pre post 5 (ns++xs) ys out := by
  have h3 : ∀ b, RegisterBits.step (program pre post) (edge pre post 3 (true::false::ns++xs) ys out) b=
      cfg pre post 4 (false::ns++xs) ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h4 : ∀ b, RegisterBits.step (program pre post) (edge pre post 4 (false::ns++xs) ys out) b=
      cfg pre post 5 (ns++xs) ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+(2+1)) = _
  rw [advance_add,wait_two pre post 3 4 (by decide) (by decide) (by decide) _ _ _ _ _ h3,
    advance_add,wait_two pre post 4 5 (by decide) (by decide) (by decide) _ _ _ _ _ h4]
  exact skip_step pre post 5 (by decide) (by decide) (by decide) _ _ _ _
 theorem toss_false (xs ys out : List Bool) :
    RegisterBits.step (program pre post) (edge pre post 5 xs ys out) false=cfg pre post 8 xs (false::ys) out := by
  rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem toss_true (xs ys out : List Bool) :
    RegisterBits.step (program pre post) (edge pre post 5 xs ys out) true=cfg pre post 6 xs (false::ys) out := by
  rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem cons_false (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 8 xs (false::ys) out) 2=cfg pre post 3 xs (consCode false++ys) out := by
  apply wait_two pre post 8 3 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem cons_true (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 6 xs (false::ys) out) 6=cfg pre post 3 xs (consCode true++ys) out := by
  have h6 : ∀ b, RegisterBits.step (program pre post) (edge pre post 6 xs (false::ys) out) b=
      cfg pre post 7 xs (false::false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h7 : ∀ b, RegisterBits.step (program pre post) (edge pre post 7 xs (false::false::ys) out) b=
      cfg pre post 8 xs (true::false::false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+(2+2)) = _
  rw [advance_add,wait_two pre post 6 7 (by decide) (by decide) (by decide) _ _ _ _ _ h6,
    advance_add,wait_two pre post 7 8 (by decide) (by decide) (by decide) _ _ _ _ _ h7]
  apply wait_two pre post 8 3 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
end MeanPayoff.RandomTable

end

section
namespace MeanPayoff.RandomTable
open RegisterBits BinaryData TreeDevice RandomTree
open BinaryData.Take (advance_add config_ext)
variable (pre post : RegisterBits.Program 5)
 theorem loop_zero (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 3 (false::xs) ys out) 2=cfg pre post 9 xs ys out := by
  apply wait_two pre post 3 9 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem pair_up (xs out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 10 xs [] out) 2=cfg pre post 11 (true::xs) [] out := by
  apply wait_two pre post 10 11 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem moves (x : Data) (xs out : List Bool) :
    ∃ n≤6*treeSize x+4, ∀ bits, advance (program pre post) bits
      (cfg pre post 9 xs (encode x) out) n=cfg pre post 10 (encode x++xs) [] out := by
  apply Flow.quiet_hop_all (flow pre post) (9 : Fin 12) (by intro q top bit; rfl)
    (core xs (encode x) []) (core (encode x++xs) [] []) out out (6*treeSize x+3)
  · intro bits
    change advance (moveCode 1 0) bits ⟨some (moveCode 1 0).start,core xs (encode x) [],out⟩ _ = _
    convert move10 x [] xs [] out bits using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [List.append_nil] ; try rfl)
  · intro b
    change RegisterBits.step _ (edge pre post 9 (encode x++xs) [] out) b=_
    rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
 theorem finishes (hq : CoinFree post) (x : Data) (out result : List Bool) (N : ℕ)
    (h : ∀ bits, advance post bits ⟨some post.start,store x [],out⟩ N=⟨none,core [] [] [],result⟩) :
    ∃ n≤N+1, ∀ bits, advance (program pre post) bits (cfg pre post 11 (encode x) [] out) n=
      ⟨none,core [] [] [],result⟩ := by
  have he : ∀ b, RegisterBits.step (Flow.compile (flow pre post))
      (Flow.edge (flow pre post) (11 : Fin 12) (core [] [] []) result) b=
      ⟨none,core [] [] [],result⟩ := by intro b; exact boundary pre post 11 [] [] result b
  obtain ⟨n,hn,hh⟩ := Flow.quiet_hop_all (flow pre post) (11 : Fin 12) hq
    (store x []) (core [] [] []) out result N h _ he
  refine ⟨n,hn,fun bits => ?_⟩
  simpa only [program,cfg,store,List.append_nil,core] using hh bits
 theorem list_size (bs : List Bool) : treeSize (listData bs)≤4*bs.length+1 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    change (encode (listData (b::bs))).length≤_
    rw [encode_list_cons,List.length_append,List.length_cons]
    have h := consCode_length_le b
    change (encode (listData bs)).length≤_ at ih
    omega
 theorem sample_trace (hq : CoinFree post) (x : Data) (result : List Bool→List Bool) (U N : ℕ)
    (hp : ∀ bs, bs.length=U → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) x) [],[]⟩ N=
        ⟨none,core [] [] [],result bs⟩) (n : ℕ) (bs : List Bool) (hn : n+bs.length=U) :
    ∃ t : RandomTree (Config (program pre post)),
      Traces (program pre post) (cfg pre post 3
        (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))++encode x) (encode (listData bs)) []) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤12*n+24*U+N+15 ∧
      ∀ f : Config (program pre post)→ℚ, t.expect f=(FairBits.acc n bs).expect
        (fun cs => f ⟨none,core [] [] [],result cs⟩) := by
  induction n generalizing bs with
  | zero =>
    obtain ⟨a,ha,ea⟩ := moves pre post (listData bs) (encode x) []
    obtain ⟨b,hb,eb⟩ := finishes pre post hq (.pair (listData bs) x) [] (result bs) N (hp bs (by omega))
    let d : Config (program pre post) := ⟨none,core [] [] [],result bs⟩
    let t : RandomTree (Config (program pre post)) := wait (2+a+2+b) (.leaf d)
    refine ⟨t,?_,?_,?_,?_⟩
    · apply Traces.wait _ ?_ (Traces.leaf d)
      intro bits
      change advance _ bits (cfg pre post 3 (false::encode x) (encode (listData bs)) []) (2+a+2+b)=d
      rw [advance_add,advance_add,advance_add,loop_zero,ea,pair_up]
      exact eb _
    · simp [t,All,d]
    · simp only [t,depth_wait,bitDepth,Nat.add_zero]
      have hs := list_size bs
      omega
    · intro f; simp only [t,expect_wait,expect,FairBits.acc]; rfl
  | succ n ih =>
    obtain ⟨l,hl,hal,hdl,hel⟩ := ih (false::bs) (by simp only [List.length_cons]; omega)
    obtain ⟨r,hr,har,hdr,her⟩ := ih (true::bs) (by simp only [List.length_cons]; omega)
    let t := wait 5 (RandomTree.coin (wait 2 l) (wait 6 r))
    refine ⟨t,?_,?_,?_,?_⟩
    · refine Traces.wait (d:=edge pre post 5
          (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))++encode x)
          (encode (listData bs)) []) 5 ?_ ?_
      · intro bits
        exact loop_one pre post (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))) (encode x) (encode (listData bs)) [] bits
      · apply Traces.coin
        · rw [toss_false]
          apply Traces.wait 2 (cons_false pre post _ _ [])
          simpa only [encode_list_cons] using hl
        · rw [toss_true]
          apply Traces.wait 6 (cons_true pre post _ _ [])
          simpa only [encode_list_cons] using hr
    · simp only [t,all_wait,All]; exact ⟨hal,har⟩
    · simp only [t,depth_wait,bitDepth]
      omega
    · intro f
      simp only [t,expect_wait,expect,FairBits.acc,hel,her]
 theorem begin_steps (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 1 (true::xs) ys out) 4=
      cfg pre post 3 xs (false::ys) out := by
  have h1 : ∀ b, RegisterBits.step (program pre post) (edge pre post 1 (true::xs) ys out) b=
      cfg pre post 2 xs ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h2 : ∀ b, RegisterBits.step (program pre post) (edge pre post 2 xs ys out) b=
      cfg pre post 3 xs (false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+2)=_
  rw [advance_add,wait_two pre post 1 2 (by decide) (by decide) (by decide) _ _ _ _ _ h1]
  exact wait_two pre post 2 3 (by decide) (by decide) (by decide) _ _ _ _ _ h2 _
 theorem complete_trace (hpre : CoinFree pre) (hpost : CoinFree post)
    (input : List Bool) (x : Data) (result : List Bool→List Bool) (U A B : ℕ)
    (hp : ∀ bits, advance pre bits ⟨some pre.start,core input [] [],[]⟩ A=
      ⟨none,store (.pair (listTree (fun _ : Unit => Data.nil) (List.replicate U ())) x) [],[]⟩)
    (hq : ∀ bs, bs.length=U → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) x) [],[]⟩ B=
        ⟨none,core [] [] [],result bs⟩) :
    ∃ t : RandomTree (Config (program pre post)),
      Traces (program pre post) (cfg pre post 0 input [] []) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤A+36*U+B+20 ∧
      ∀ f : Config (program pre post)→ℚ, t.expect f=(FairBits.acc U []).expect
        (fun cs => f ⟨none,core [] [] [],result cs⟩) := by
  let z := Data.pair (listTree (fun _ : Unit => Data.nil) (List.replicate U ())) x
  have he : ∀ b, RegisterBits.step (Flow.compile (flow pre post))
      (Flow.edge (flow pre post) (0 : Fin 12) (store z []) []) b=
      cfg pre post 1 (encode z) [] [] := by
    intro b
    change RegisterBits.step _ (edge pre post 0 (encode z++[]) [] []) b=_
    rw [List.append_nil,boundary]
    apply config_ext <;> (try rfl)
    funext i; fin_cases i <;> rfl
  obtain ⟨a,ha,ea⟩ := Flow.quiet_hop_all (flow pre post) (0 : Fin 12) hpre
    (core input [] []) (store z []) [] [] A hp _ he
  change ∀ bits, advance (program pre post) bits (cfg pre post 0 input [] []) a=
    cfg pre post 1 (encode z) [] [] at ea
  obtain ⟨t,ht,hal,hd,he⟩ := sample_trace pre post hpost x result U B hq U [] (by simp)
  refine ⟨wait (a+4) t,?_,by simpa only [all_wait] using hal,?_,?_⟩
  · apply Traces.wait _ ?_ ht
    intro bits
    rw [advance_add,ea]
    exact begin_steps pre post _ [] [] _
  · simp only [depth_wait]
    omega
  · intro f; rw [expect_wait,he]
end MeanPayoff.RandomTable

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Realizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
 theorem pre_quiet : CoinFree pre :=
  Sequence5.quiet _ _ Box5.quiet (Sequence5.quiet _ _ (by intro q top b; rfl) Preparation.device.quiet)
 theorem pre_runs (d : Digits) (bits : ℕ→Bool) :
    advance pre bits ⟨some pre.start,core d.bits [] [],[]⟩ (preCost d)=
      ⟨none,store (encode (Preparation.value d)) [],[]⟩ := by
  have hd : (encode d : Data)=listData d.bits := Halve.listTree_boolData _
  apply Sequence5.runs Box5.program preTail (core d.bits [] []) (core [] (BinaryData.encode (encode d)) [])
    (store (encode (Preparation.value d)) []) [] [] _ _ ?_ ?_ bits
  · intro cs; rw [hd]; exact Box5.runs d.bits [] cs
  · intro cs
    apply Sequence5.runs (moveCode 1 0) Preparation.device.program _ (store (encode d) []) _ [] [] _ _ ?_ ?_ cs
    · intro ds
      convert move10 (encode d) [] [] [] [] ds using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [store,core,List.append_nil])
    · exact Preparation.device.correct d [] []
 theorem post_quiet : CoinFree post := Sequence5.quiet _ _ PostCode.run.device.quiet Emit.quiet
 theorem post_runs (z : PostCode.Input) (bits : ℕ→Bool) :
    advance post bits ⟨some post.start,store (encode z) [],[]⟩ (postCost z)=
      ⟨none,core [] [] [],(PostCode.run z).bits⟩ := by
  apply Sequence5.runs PostCode.run.device.program Emit.program _ (store (encode (PostCode.run z)) []) _ [] _ _ _
    (PostCode.run.device.correct z [] []) ?_ bits
  intro cs
  have hd : (encode (PostCode.run z) : Data)=listData (PostCode.run z).bits := Halve.listTree_boolData _
  convert Emit.runs (PostCode.run z).bits [] [] cs using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [List.nil_append,hd] ; try rfl)
 theorem digits_length (d : Digits) : d.bits.length≤treeSize (encode d) := by
  have h := list_length_le_size boolData d.bits
  change d.bits.length≤treeSize (listTree boolData d.bits)
  omega
 theorem post_polynomial : ∃ K e, ∀ z, postCost z≤K*(treeSize (encode z)+1)^e := by
  have hi := PolyBound.base (fun z : PostCode.Input => treeSize (encode z))
  have hc := polynomial_limit PostCode.run.polynomial _ (fun z : PostCode.Input => z) hi
  have ho := polynomial_output PostCode.run.device _ (fun z : PostCode.Input => z) hi hc
  have he := ((PolyBound.const _ 4).mul ho).add (PolyBound.const _ 2)
  have hb : PolyBound (fun z : PostCode.Input => treeSize (encode z)) (fun z => Emit.cost (PostCode.run z).bits) :=
    he.mono (fun z => (Emit.bound _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (digits_length _)) 2))
  exact (hc.add hb).add (PolyBound.const _ 2)
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
 theorem pre_cost_bound : PolyBound Preparation.resource preCost := by
  have hi := Preparation.input_bound
  have hl := hi.mono digits_length
  have hb : PolyBound Preparation.resource
      (fun d => 2*d.bits.length+2+feedCost d.bits+1) :=
    (((PolyBound.const _ 7).mul hl).add (PolyBound.const _ 3)).mono (fun d => Box.boxes_bound d.bits)
  exact (((hb.add ((PolyBound.const _ 6).mul hi)).add (PolyBound.const _ 3)).add
    Preparation.cost_bound).add (PolyBound.const _ 4) |>.mono (by intro d; unfold preCost; omega)
 theorem amount_bound : PolyBound Preparation.resource amount :=
  Preparation.output_bound.mono (fun d => (Size.length _).trans (Size.fst (Preparation.value d)))
 theorem aux_bound : PolyBound Preparation.resource (fun d => treeSize (encode (aux d))) :=
  Preparation.output_bound.mono (fun d => Size.snd (Preparation.value d))
 theorem input_size (d : Digits) (bs : List Bool) :
    treeSize (encode ((⟨bs⟩ : Digits),aux d))≤4*bs.length+treeSize (encode (aux d))+2 := by
  change treeSize (.pair (listTree boolData bs) (encode (aux d)))≤_
  rw [Halve.listTree_boolData,treeSize_pair]
  have h := RandomTable.list_size bs
  omega
 theorem post_budget (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (d : Digits) (bs : List Bool) (hl : bs.length=amount d) :
    postCost (⟨bs⟩,aux d)≤postBudget K e d := by
  apply (h _).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hi := input_size d bs
  rw [hl] at hi
  omega
 theorem budget_bound (K e : ℕ) : PolyBound Preparation.resource (postBudget K e) :=
  (PolyBound.const _ K).mul (((((PolyBound.const _ 4).mul amount_bound).add aux_bound).add
    (PolyBound.const _ 3)).pow e)
 theorem limit_bound (K e : ℕ) : PolyBound Preparation.resource (limit K e) :=
  ((pre_cost_bound.add ((PolyBound.const _ 36).mul amount_bound)).add (budget_bound K e)).add (PolyBound.const _ 20)
 theorem trace (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e) (d : Digits) :
    ∃ t : RandomTree (Config program), Traces program (RegisterBits.initial program d.bits) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤limit K e d ∧
      ∀ f : Config program→ℚ, t.expect f=(FairBits.acc (amount d) []).expect
        (fun bs => f ⟨none,core [] [] [],answer d bs⟩) := by
  have hu : (Preparation.value d).1=List.replicate (amount d) () :=
    List.eq_replicate_of_mem (fun _ _ => Subsingleton.elim _ _)
  have hp : ∀ bits, advance pre bits ⟨some pre.start,core d.bits [] [],[]⟩ (preCost d)=
      ⟨none,store (.pair (listTree (fun _ : Unit => Data.nil) (List.replicate (amount d) ())) (encode (aux d))) [],[]⟩ := by
    intro bits
    have hv : encode (Preparation.value d)=Data.pair
        (listTree (fun _ : Unit => Data.nil) (List.replicate (amount d) ())) (encode (aux d)) := by
      change Data.pair (encode (Preparation.value d).1) (encode (aux d))=_
      rw [hu]
      rfl
    simpa only [hv] using pre_runs d bits
  have hq : ∀ bs, bs.length=amount d → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) (encode (aux d))) [],[]⟩ (postBudget K e d)=
      ⟨none,core [] [] [],answer d bs⟩ := by
    intro bs hl bits
    have hr := post_runs (⟨bs⟩,aux d) bits
    apply advance_pad _ _ _ bits (post_budget K e h d bs hl) ?_ rfl
    have hv : encode ((⟨bs⟩ : Digits),aux d)=Data.pair (listData bs) (encode (aux d)) := by
      change Data.pair (listTree boolData bs) _=_
      rw [Halve.listTree_boolData]
    simpa only [hv,answer] using hr
  obtain ⟨t,ht,hh,hd,he⟩ := RandomTable.complete_trace pre post pre_quiet post_quiet d.bits
    (encode (aux d)) (answer d) (amount d) (preCost d) (postBudget K e d) hp hq
  refine ⟨t,?_,hh,hd,he⟩
  have hi : RegisterBits.initial program d.bits=RandomTable.cfg pre post 0 d.bits [] [] := by
    apply BinaryData.Take.config_ext <;> (try rfl)
    funext i; fin_cases i <;> rfl
  rw [hi]
  exact ht
end MeanPayoff.Realizer

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Complexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
 theorem total_formula (K e : ℕ) (d : Digits) :
    total K e d=2*(3*d.bits.length+8+limit K e d*(4*(d.bits.length+limit K e d)+16)) := by
  have hs : storeSize (RegisterBits.initial program d.bits).stack=d.bits.length := by
    simp [storeSize,RegisterBits.initial,Fin.sum_univ_succ]
  simp only [total,Compile.bound,Compile.overhead,hs]
 theorem total_bound (K e : ℕ) : PolyBound Preparation.resource (total K e) := by
  have hl := Preparation.input_bound.mono digits_length
  have hn := limit_bound K e
  apply ((PolyBound.const _ 2).mul
    ((((PolyBound.const _ 3).mul hl).add (PolyBound.const _ 8)).add
      (hn.mul ((((PolyBound.const _ 4).mul (hl.add hn)).add (PolyBound.const _ 16)))))).mono
  intro d
  rw [total_formula]
 theorem resource_quasi (d : Digits) :
    Preparation.resource d+1≤2^(25003*(Nat.clog 2 (d.bits.length+2))^2) := by
  let h := Nat.clog 2 (d.bits.length+2)
  have hh : 1≤h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1<2)).mpr
    simp only [pow_zero]
    omega
  have hl : d.bits.length≤2^h := (Nat.le_add_right _ 2).trans (Nat.le_pow_clog (by norm_num) _)
  have he : h≤25000*h^2 := by nlinarith only [hh]
  have hp := hl.trans (Nat.pow_le_pow_right (by norm_num : 1≤2) he)
  have hx : treeSize (encode d)≤4*d.bits.length+1 := by
    change treeSize (listTree boolData d.bits)≤_
    rw [Halve.listTree_boolData]
    exact RandomTable.list_size _
  have hpos : 1≤2^(25000*h^2) := Nat.one_le_pow _ _ (by norm_num)
  calc
    Preparation.resource d+1≤8*2^(25000*h^2) := by
      unfold Preparation.resource
      rw [Preparation.exponent_length]
      change treeSize (encode d)+2^(25000*h^2)+1≤_
      omega
    _ = 2^(25000*h^2+3) := by rw [pow_add]; ring
    _ ≤ 2^(25003*h^2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hh])
 theorem polynomial_quasi {f : Digits→ℕ} (hf : PolyBound Preparation.resource f) :
    ∃ C : ℕ, ∀ d, f d≤2^(C*(Nat.clog 2 (d.bits.length+2))^2) := by
  obtain ⟨K,e,hf⟩ := hf
  refine ⟨K+25003*e,fun d => ?_⟩
  let h := Nat.clog 2 (d.bits.length+2)
  have hh : 1≤h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1<2)).mpr
    simp only [pow_zero]
    omega
  have hk : K≤2^K := Nat.lt_two_pow_self.le
  calc
    f d ≤ K*(Preparation.resource d+1)^e := hf d
    _ ≤ 2^K*(2^(25003*h^2))^e := Nat.mul_le_mul hk (Nat.pow_le_pow_left (resource_quasi d) e)
    _ = 2^(K+25003*h^2*e) := by rw [←pow_mul,pow_add]
    _ ≤ 2^((K+25003*e)*h^2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hs : 1≤h^2 := by nlinarith
      have hm := Nat.mul_le_mul_left K hs
      nlinarith only [hm]
 theorem natural_quasi_real {f : Digits→ℕ} (C : ℕ)
    (hf : ∀ d, f d≤2^(C*(Nat.clog 2 (d.bits.length+2))^2)) :
    ∃ D : ℝ, 0<D ∧ ∀ d, (f d : ℝ)≤(2 : ℝ)^(D*(Real.logb 2 (d.bits.length+2))^2) := by
  refine ⟨4*C+1,by positivity,fun d => ?_⟩
  have hc := clog_real_le_twice_logb d.bits.length
  have hc0 : (0 : ℝ)≤(Nat.clog 2 (d.bits.length+2) : ℝ) := Nat.cast_nonneg _
  have hl0 : 0≤Real.logb 2 (d.bits.length+2) := by linarith only [hc,hc0]
  have hs : ((Nat.clog 2 (d.bits.length+2) : ℝ))^2≤4*(Real.logb 2 (d.bits.length+2))^2 := by
    nlinarith only [hc,hc0,hl0]
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg C : (0 : ℝ)≤C)
  have hb : (f d : ℝ)≤(2 : ℝ)^(C*(Nat.clog 2 (d.bits.length+2))^2) := by exact_mod_cast hf d
  apply hb.trans
  rw [←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
  simp only [Nat.cast_mul,Nat.cast_pow]
  nlinarith only [hm,sq_nonneg (Real.logb 2 (d.bits.length+2))]
 theorem total_quasi (K e : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ d,
    (total K e d : ℝ)≤(2 : ℝ)^(C*(Real.logb 2 (d.bits.length+2))^2) := by
  obtain ⟨C,hC⟩ := polynomial_quasi (total_bound K e)
  exact natural_quasi_real C hC
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified RandomTree
 theorem tree_halts (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e) (d : Digits) :
    (tree program (limit K e d) (RegisterBits.initial program d.bits)).All (fun c => c.control=none) := by
  obtain ⟨t,ht,hh,hd,_⟩ := trace K e h d
  exact ht.tree_all hh hd
 theorem tree_success (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e) (G : Game) :
    7/8≤(tree program (limit K e ⟨input G⟩) (RegisterBits.initial program (input G))).probability
      (fun c => BinaryInput.CorrectList G c.output) := by
  classical
  unfold probability
  rw [tree_law K e h G (fun out => if BinaryInput.CorrectList G out then 1 else 0)]
  simpa only [probability,BinaryInput.correctList_ofFn] using gameSolve_success G

end MeanPayoff.Realizer

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits.Compile
open BinaryData
open scoped Classical
 theorem correct_probability {K : ℕ} (P : Program K) (G : Game) (n : ℕ)
    (hh : (tree P n (RegisterBits.initial P (input G))).All (fun c => c.control=none)) :
    (2:ℚ)^(2*bound P (input G) n)*
      (tree P n (RegisterBits.initial P (input G))).probability (fun c => BinaryInput.CorrectList G c.output)≤
    ((Finset.univ.filter (fun bits : Fin (2*bound P (input G) n)→Bool =>
      CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card : ℚ) := by
  classical
  have hp := machine_probability P (input G) n hh (BinaryInput.CorrectList G)
  apply hp.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro bits hb
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
  obtain ⟨out,ho,hhalt,ht⟩ := hb
  exact correctList_packet G (machine P) _ out ho hhalt ht
 theorem correct_count {K : ℕ} (P : Program K) (G : Game) (n : ℕ)
    (hh : (tree P n (RegisterBits.initial P (input G))).All (fun c => c.control=none))
    (hp : 7/8≤(tree P n (RegisterBits.initial P (input G))).probability
      (fun c => BinaryInput.CorrectList G c.output)) :
    7*2^(2*bound P (input G) n)≤8*(Finset.univ.filter
      (fun bits : Fin (2*bound P (input G) n)→Bool =>
        CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card := by
  classical
  have hq := correct_probability P G n hh
  have hl : (2:ℚ)^(2*bound P (input G) n)*(7/8)≤
      ((Finset.univ.filter (fun bits : Fin (2*bound P (input G) n)→Bool =>
        CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card : ℚ) :=
    (mul_le_mul_of_nonneg_left hp (by positivity)).trans hq
  have hr : (7:ℚ)*2^(2*bound P (input G) n)≤8*
      ((Finset.univ.filter (fun bits : Fin (2*bound P (input G) n)→Bool =>
        CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card : ℚ) := by
    linarith only [hl]
  exact_mod_cast hr
 theorem halt_all {K : ℕ} (P : Program K) (G : Game) (n : ℕ)
    (hh : (tree P n (RegisterBits.initial P (input G))).All (fun c => c.control=none))
    (bits : Fin (2*bound P (input G) n)→Bool) :
    (result (machine P) G (2*bound P (input G) n) bits).control=none :=
  (machine_packet P (input G) n hh bits).1
end MeanPayoff.RegisterBits.Compile

end

section
namespace MeanPayoff

theorem main : MainClaim := by
  obtain ⟨K,e,h⟩ := Realizer.post_polynomial
  obtain ⟨C,hC,hbound⟩ := Realizer.total_quasi K e
  refine ⟨RegisterBits.Compile.machine Realizer.program,C,hC,fun G =>
    ⟨Realizer.total K e ⟨input G⟩,hbound ⟨input G⟩,?_,?_⟩⟩
  · exact RegisterBits.Compile.halt_all Realizer.program G (Realizer.limit K e ⟨input G⟩)
      (Realizer.tree_halts K e h ⟨input G⟩)
  · exact RegisterBits.Compile.correct_count Realizer.program G (Realizer.limit K e ⟨input G⟩)
      (Realizer.tree_halts K e h ⟨input G⟩) (Realizer.tree_success K e h G)
end MeanPayoff

theorem randomized_quasipolynomial_mean_payoff_oai : MeanPayoff.MainClaim := MeanPayoff.main

end

end OAI
end

theorem solution : type_of% @OAI.randomized_quasipolynomial_mean_payoff_oai := @OAI.randomized_quasipolynomial_mean_payoff_oai
