-- Prove2me | solution 1 for SensitivityVariableFrontier.search_correct
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-29T00:20:28.193193+00:00
-- url     : https://prove2.me/submissions/f4a3fb53-5da9-4300-8d17-837163059bea

import Definitions.Def_SensitivityVariableFrontier


/-! Complete exact finite-alphabet search, preserving witnesses under dominance pruning.
The recurrence monotonicity and normalization proofs reuse the local orbit-law work;
the raw recurrence retains the attribution in Def_SensitivityProfileCycle. -/


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.all false


namespace VariableFrontierCostLemmas
open SensitivityProfileCycle SensitivityProfileSearch
variable {n : ℕ}


@[gcongr] theorem targetCost_mono (q v a b a' b' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') :
    targetCost q v a b ≤ targetCost q v a' b' := by
  unfold targetCost
  gcongr

@[gcongr] theorem coupledCost_mono (q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    coupledCost q v a b c e ≤ coupledCost q v a' b' c' e' := by
  unfold coupledCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  split_ifs <;> gcongr

@[gcongr] theorem ordinaryCost_mono (q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    ordinaryCost q v a b c e ≤ ordinaryCost q v a' b' c' e' := by
  unfold ordinaryCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  apply Finset.sup_mono_fun
  intro z hz
  split_ifs <;> gcongr

@[gcongr] theorem sourceCost_mono (v w a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    sourceCost v w a b c e ≤ sourceCost v w a' b' c' e' := by
  unfold sourceCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  apply Finset.sup_mono_fun
  intro z hz
  split_ifs <;> gcongr

@[gcongr] theorem strictSourceCost_mono (t w a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    strictSourceCost t w a b c e ≤ strictSourceCost t w a' b' c' e' := by
  unfold strictSourceCost
  gcongr

@[gcongr] theorem dedupCost_mono (internal : ℕ → ℕ) (q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    dedupCost internal q v a b c e ≤ dedupCost internal q v a' b' c' e' := by
  unfold dedupCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  apply Finset.sup_mono_fun
  intro z hz
  split_ifs <;> gcongr

@[gcongr] theorem ordinaryDedupInternalCost_mono (r q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    ordinaryDedupInternalCost r q v a b c e ≤ ordinaryDedupInternalCost r q v a' b' c' e' := by
  unfold ordinaryDedupInternalCost
  gcongr

@[gcongr] theorem rawOne_mono (h : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawOne h C Z Y i j ≤ rawOne h C Z' Y' i j := by
  unfold rawOne
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroCoupled_mono (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroCoupled k t v C Z Y i j ≤ rawZeroCoupled k t v C Z' Y' i j := by
  unfold rawZeroCoupled
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroOrdinary_mono (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroOrdinary k t v C Z Y i j ≤ rawZeroOrdinary k t v C Z' Y' i j := by
  unfold rawZeroOrdinary
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroSource_mono (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroSource k t v w C Z Y i j ≤ rawZeroSource k t v w C Z' Y' i j := by
  unfold rawZeroSource
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroSourceFull_mono (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroSourceFull k t v w C Z Y i j ≤ rawZeroSourceFull k t v w C Z' Y' i j := by
  unfold rawZeroSourceFull
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroDedupBoth_mono (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroDedupBoth k t v C Z Y i j ≤ rawZeroDedupBoth k t v C Z' Y' i j := by
  unfold rawZeroDedupBoth
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroSourceCombined_mono (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroSourceCombined k t v w C Z Y i j ≤ rawZeroSourceCombined k t v w C Z' Y' i j := by
  unfold rawZeroSourceCombined
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY


end VariableFrontierCostLemmas

namespace SensitivityVariableWord
open VariableFrontierCostLemmas SensitivityProfileCycle SensitivityProfileSearch
variable {n : ℕ} {G : GraphData}


def ProfileLE (P Q : Profile n) : Prop :=
  ∀ i j, P.zero i j ≤ Q.zero i j ∧ P.one i j ≤ Q.one i j

theorem envelope_mono (A B : Matrix n) (h : ∀ i j, A i j ≤ B i j)
    (i j : Fin n) : envelope A i j ≤ envelope B i j := by
  unfold envelope
  split_ifs with hij
  · exact Finset.inf'_mono_fun (fun ab _ => h ab.1 ab.2)
  · exact le_rfl

theorem envelope_le (A : Matrix n) (i j : Fin n) :
    envelope A i j ≤ A i j := by
  unfold envelope
  split_ifs with hij
  · exact Finset.inf'_le (b := (i,j)) _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hij, le_rfl⟩)
  · exact Nat.zero_le _

theorem envelope_interval (A : Matrix n) (i j a b : Fin n)
    (hia : i ≤ a) (hab : a ≤ b) (hbj : b ≤ j) :
    envelope A i j ≤ envelope A a b := by
  have hij : i ≤ j := hia.trans (hab.trans hbj)
  simp only [envelope, dif_pos hij, dif_pos hab]
  apply Finset.le_inf'
  intro cd hcd
  have hcd' := (Finset.mem_filter.mp hcd).2
  apply Finset.inf'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hia.trans hcd'.1, hcd'.2.1, hcd'.2.2.trans hbj⟩

theorem envelope_idempotent (A : Matrix n) : envelope (envelope A) = envelope A := by
  funext i j
  apply le_antisymm (envelope_le (envelope A) i j)
  unfold envelope at ⊢
  split_ifs with hij
  · apply Finset.le_inf'
    intro ab hab
    have hab' := (Finset.mem_filter.mp hab).2
    simpa only [envelope, dif_pos hij] using
      envelope_interval A i j ab.1 ab.2 hab'.1 hab'.2.1 hab'.2.2
  · exact le_rfl

theorem normalize_idempotent (P : Profile n) : normalize (normalize P) = normalize P := by
  simp only [SensitivityProfileSearch.normalize, envelope_idempotent]

theorem normalize_step (C : Recipe n) (P : Profile n) :
    normalize (SensitivityVariableWord.step G C P) = SensitivityVariableWord.step G C P := by
  simp only [SensitivityProfileSearch.normalize, SensitivityVariableWord.step, envelope_idempotent]

theorem step_mono (C : Recipe n) (P Q : Profile n) (h : ProfileLE P Q) :
    ProfileLE (SensitivityVariableWord.step G C P) (SensitivityVariableWord.step G C Q) := by
  intro i j
  constructor
  · apply envelope_mono
    intro a b
    exact rawZeroSourceCombined_mono _ _ _ _ C _ _ _ _
      (fun x y => (h x y).1) (fun x y => (h x y).2) a b
  · apply envelope_mono
    intro a b
    exact rawOne_mono _ C _ _ _ _
      (fun x y => (h x y).1) (fun x y => (h x y).2) a b

theorem normalize_fold (word : List (Recipe n)) (P : Profile n)
    (hP : normalize P = P) :
    normalize (word.foldl (fun A C => SensitivityVariableWord.step G C A) P) =
      word.foldl (fun A C => SensitivityVariableWord.step G C A) P := by
  induction word generalizing P with
  | nil => exact hP
  | cons C word ih => exact ih (SensitivityVariableWord.step G C P) (normalize_step C P)

theorem normalize_run (word : List (Recipe n)) (P : Profile n) :
    normalize (SensitivityVariableWord.run G word P) = SensitivityVariableWord.run G word P :=
  normalize_fold word _ (normalize_idempotent P)

theorem run_append (word₁ word₂ : List (Recipe n)) (P : Profile n) :
    SensitivityVariableWord.run G (word₁ ++ word₂) P = SensitivityVariableWord.run G word₂ (SensitivityVariableWord.run G word₁ P) := by
  change (word₁ ++ word₂).foldl (fun A C => SensitivityVariableWord.step G C A) (normalize P) =
    word₂.foldl (fun A C => SensitivityVariableWord.step G C A) (normalize (SensitivityVariableWord.run G word₁ P))
  rw [normalize_run, List.foldl_append]
  rfl

theorem le_height (P : Profile n) (i j : Fin n) :
    P.zero i j ≤ height P ∧ P.one i j ≤ height P := by
  have h : max (P.zero i j) (P.one i j) ≤
      Finset.univ.sup (fun ij : Fin n × Fin n => max (P.zero ij.1 ij.2) (P.one ij.1 ij.2)) :=
    Finset.le_sup (f := fun ij : Fin n × Fin n =>
      max (P.zero ij.1 ij.2) (P.one ij.1 ij.2)) (Finset.mem_univ (i,j))
  exact ⟨(le_max_left _ _).trans (h.trans (le_max_right _ _)),
    (le_max_right _ _).trans (h.trans (le_max_right _ _))⟩

theorem height_le {P : Profile n} {B : ℕ} (hB : 2 ≤ B)
    (h : ∀ i j, P.zero i j ≤ B ∧ P.one i j ≤ B) : height P ≤ B := by
  apply max_le hB
  apply Finset.sup_le
  intro ij _
  exact max_le (h ij.1 ij.2).1 (h ij.1 ij.2).2

end SensitivityVariableWord


set_option autoImplicit false

namespace FiniteDominance
variable {α : Type} (R : α → α → Prop) [DecidableRel R]

theorem insert_mem {x y : α} {s : List α}
    (hy : y ∈ insert R x s) : y = x ∨ y ∈ s := by
  unfold insert at hy
  split at hy
  · exact Or.inr hy
  · rcases List.mem_cons.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.mp h).1

theorem insert_cover (hrefl : Reflexive R) {x y : α} {s : List α}
    (hy : y = x ∨ y ∈ s) : ∃ z ∈ insert R x s, R z y := by
  unfold insert
  split
  · rename_i h
    rcases hy with rfl | hy
    · exact h
    · exact ⟨y, hy, hrefl y⟩
  · rcases hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hrefl _⟩
    · by_cases hxy : R x y
      · exact ⟨x, List.mem_cons_self, hxy⟩
      · exact ⟨y, List.mem_cons_of_mem _ (by simp [hy, hxy]), hrefl y⟩

theorem prune_mem {s : List α} {x : α} (hx : x ∈ prune R s) : x ∈ s := by
  induction s with
  | nil => exact hx
  | cons y s ih =>
    rcases insert_mem R hx with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons.mpr (Or.inr (ih h))

theorem prune_cover (hrefl : Reflexive R) (htrans : Transitive R)
    {s : List α} {x : α} (hx : x ∈ s) : ∃ y ∈ prune R s, R y x := by
  induction s with
  | nil => cases hx
  | cons z s ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact insert_cover R hrefl (Or.inl rfl)
    · obtain ⟨y, hy, hyx⟩ := ih hx
      obtain ⟨w, hw, hwy⟩ := insert_cover R hrefl (Or.inr hy)
      exact ⟨w, hw, htrans hwy hyx⟩

end FiniteDominance


set_option autoImplicit false
set_option maxRecDepth 10000

namespace SensitivityVariableFinite
open SensitivityProfileCycle SensitivityProfileSearch SensitivityVariableWord

variable {n : ℕ} {G : GraphData}

def canonical (C : Recipe n) : Recipe n :=
  { C with tol := fun i => if 3 ≤ i.val then C.tol i else 0 }

theorem canonical_valid (C : Recipe n) (h : C.Valid) : (canonical C).Valid := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro i j hij hi
  have hj : 3 ≤ j.val := le_trans hi hij
  simpa [canonical, hi, hj] using h.2.2 i j hij hi

theorem toleranceCount_pos (G : GraphData) : 0 < G.toleranceCount := by
  by_contra h
  have hzero : G.toleranceCount = 0 := Nat.eq_zero_of_not_pos h
  have hz : extendCutoffs G.cutoffs 0 = 0 := by
    unfold extendCutoffs
    simp [hzero]
  have hordinary : G.ordinaryCutoff = 0 := G.cutoff_zero.symm.trans hz
  have hfour := G.ordinary_ge_four
  omega

theorem canonical_bounded (C : Recipe n)
    (h : ∀ i, 3 ≤ i.val → 0 < C.tol i → C.tol i < G.toleranceCount) :
    ∀ i, (canonical C).tol i < G.toleranceCount := by
  intro i
  by_cases hi : 3 ≤ i.val
  · by_cases hp : 0 < C.tol i
    · simpa [canonical, hi] using h i hi hp
    · simpa [canonical, hi, Nat.eq_zero_of_not_pos hp] using toleranceCount_pos G
  · simpa [canonical, hi] using toleranceCount_pos G

theorem canonical_rawOne (C : Recipe n) (Z Y : Matrix n) (h : ℕ)
    (i j : Fin n) (hij : i ≤ j) :
    rawOne h (canonical C) Z Y i j = rawOne h C Z Y i j := by
  by_cases hj : j.val < 3
  · simp [rawOne, hj, canonical]
  · by_cases hi : i.val < 3
    · simp [rawOne, hj, hi, canonical]
    · have hi' : 3 ≤ i.val := by omega
      have hj' : 3 ≤ j.val := by omega
      simp [rawOne, hj, hi, canonical, hi', hj']

theorem canonical_rawZero (C : Recipe n) (Z Y : Matrix n)
    (k t w : ℕ) (v : ℕ → ℕ) (i j : Fin n) (hij : i ≤ j) :
    rawZeroSourceCombined k t v w (canonical C) Z Y i j =
      rawZeroSourceCombined k t v w C Z Y i j := by
  by_cases hj : j.val < 3
  · have hi : i.val < 3 := lt_of_le_of_lt hij hj
    have hi' : ¬ 3 ≤ i.val := by omega
    simp [rawZeroSourceCombined, rawZeroSourceFull, rawZeroSource,
      rawZeroOrdinary, rawZeroDedupBoth, rawZeroCoupled, hj, hi, hi', canonical]
  · have hj' : 3 ≤ j.val := by omega
    by_cases hi : i.val < 3
    · have hi' : ¬ 3 ≤ i.val := by omega
      simp [rawZeroSourceCombined, rawZeroSourceFull, rawZeroSource,
        rawZeroOrdinary, rawZeroDedupBoth, rawZeroCoupled, hj, hi, hi', canonical, hj']
    · have hi' : 3 ≤ i.val := by omega
      simp [rawZeroSourceCombined, rawZeroSourceFull, rawZeroSource,
        rawZeroOrdinary, rawZeroDedupBoth, rawZeroCoupled, hj, hi, hi', canonical, hj']

theorem envelope_congr_upper (A B : Matrix n)
    (h : ∀ i j, i ≤ j → A i j = B i j) : envelope A = envelope B := by
  funext i j
  unfold envelope
  split
  · apply Finset.inf'_congr _ rfl
    intro ab hab
    exact h ab.1 ab.2 (Finset.mem_filter.mp hab).2.2.1
  · rfl

theorem canonical_step (C : Recipe n) (P : Profile n) :
    SensitivityVariableWord.step G (canonical C) P = SensitivityVariableWord.step G C P := by
  unfold SensitivityVariableWord.step
  congr 1
  · apply envelope_congr_upper
    exact canonical_rawZero C P.zero P.one G.vertices G.ordinaryCutoff G.sourceCutoff _
  · apply envelope_congr_upper
    exact canonical_rawOne C P.zero P.one G.degree

def encode (C : Recipe n)
    (h : ∀ i, 3 ≤ i.val → 0 < C.tol i → C.tol i < G.toleranceCount) : Letter G.toleranceCount n :=
  ⟨C.target, C.gate, C.aux,
    fun i => ⟨(canonical C).tol i, canonical_bounded (G := G) C h i⟩⟩

theorem encode_recipe (C : Recipe n)
    (h : ∀ i, 3 ≤ i.val → 0 < C.tol i → C.tol i < G.toleranceCount) :
    (encode (G := G) C h).recipe = canonical C := by rfl

theorem canonical_fold (word : List (Recipe n)) (P : Profile n) :
    (word.map canonical).foldl (fun Q C => SensitivityVariableWord.step G C Q) P =
      word.foldl (fun Q C => SensitivityVariableWord.step G C Q) P := by
  induction word generalizing P with
  | nil => rfl
  | cons C word ih =>
    simp only [List.map_cons, List.foldl_cons, canonical_step, ih]

theorem canonical_run (word : List (Recipe n)) (P : Profile n) :
    SensitivityVariableWord.run G (word.map canonical) P = SensitivityVariableWord.run G word P := canonical_fold word _

theorem encode_word (word : List (Recipe n)) (h : Admissible G word) :
    ∃ letters : List (Letter G.toleranceCount n),
      letters.length = word.length ∧
      (∀ C ∈ letters, C.recipe.Valid) ∧
      (∀ P, SensitivityVariableWord.run G (letters.map Letter.recipe) P = SensitivityVariableWord.run G word P) := by
  let letters := word.attach.map fun C => encode (G := G) C.val (h C.val C.property).2
  refine ⟨letters, ?_, ?_, ?_⟩
  · simp [letters]
  · intro C hC
    simp only [letters, List.mem_map] at hC
    obtain ⟨D, hD, rfl⟩ := hC
    exact canonical_valid D.val (h D.val D.property).1
  · intro P
    have heq : letters.map Letter.recipe = word.map canonical := by
      simp [letters, List.map_map, encode_recipe]
    rw [heq]
    exact canonical_run word P

theorem alphabet_admissible (letters : List (Letter G.toleranceCount n))
    (h : ∀ C ∈ letters, C.recipe.Valid) :
    Admissible G (letters.map Letter.recipe) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  refine ⟨h D hD, ?_⟩
  intro i hi hp
  exact (D.tol i).isLt

theorem crossing_iff_finite (word : List (Recipe n)) (h : Crosses215 G word) :
    ∃ letters : List (Letter G.toleranceCount n),
      letters.length = word.length ∧ Crosses215 G (letters.map Letter.recipe) := by
  obtain ⟨letters, hlen, hvalid, hrun⟩ := encode_word word h.2.1
  refine ⟨letters, hlen, ?_, alphabet_admissible letters hvalid, ?_⟩
  · intro he
    have hl := congrArg List.length he
    simp only [List.length_map, List.length_nil, hlen] at hl
    exact h.1 (List.length_eq_zero_iff.mp hl)
  · simpa only [hrun, List.length_map, hlen] using h.2.2

end SensitivityVariableFinite


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SensitivityVariableFrontier
open SensitivityProfileCycle SensitivityProfileSearch SensitivityVariableWord
open SensitivityVariableFinite
variable {n : ℕ} {G : GraphData}

theorem below_refl (P : Profile n) : Below P P := fun _ _ => ⟨le_rfl, le_rfl⟩

theorem below_trans {P Q R : Profile n} (hPQ : Below P Q) (hQR : Below Q R) :
    Below P R := fun i j => ⟨(hPQ i j).1.trans (hQR i j).1,
      (hPQ i j).2.trans (hQR i j).2⟩

theorem below_step (C : Recipe n) {P Q : Profile n} (h : Below P Q) :
    Below (SensitivityVariableWord.step G C P) (SensitivityVariableWord.step G C Q) := step_mono C P Q h

theorem below_height {P Q : Profile n} (h : Below P Q) : height P ≤ height Q := by
  apply height_le (le_max_left _ _)
  intro i j
  exact ⟨(h i j).1.trans (le_height Q i j).1,
    (h i j).2.trans (le_height Q i j).2⟩

theorem mem_maps {m : ℕ} (f : Fin n → Fin m) : f ∈ maps n m := by
  apply List.mem_map.mpr
  refine ⟨fun i _ => f i, ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (fun i _ => List.mem_finRange (f i))

theorem mem_allLetters {q : ℕ} (C : Letter q n) : C ∈ allLetters q n := by
  rcases C with ⟨t, g, a, q⟩
  apply List.mem_flatMap.mpr
  refine ⟨t, mem_maps t, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨g, mem_maps g, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨a, mem_maps a, ?_⟩
  exact List.mem_map.mpr ⟨q, mem_maps q, rfl⟩

theorem mem_alphabet {q : ℕ} (C : Letter q n) : C ∈ alphabet q n ↔ C.recipe.Valid := by
  simp [alphabet, mem_allLetters C]

theorem run_snoc (word : List (Recipe n)) (C : Recipe n) (P : Profile n) :
    SensitivityVariableWord.run G (word ++ [C]) P = SensitivityVariableWord.step G C (SensitivityVariableWord.run G word P) := by
  rw [run_append]
  change SensitivityVariableWord.step G C (normalize (SensitivityVariableWord.run G word P)) = SensitivityVariableWord.step G C (SensitivityVariableWord.run G word P)
  rw [normalize_run]

theorem frontier_sound {k : ℕ} {P : Profile n} (hP : P ∈ frontier G n k) :
    ∃ word : List (Recipe n), word.length = k ∧ Admissible G word ∧
      SensitivityVariableWord.run G word (unitProfile n) = P := by
  induction k generalizing P with
  | zero =>
    have heq : P = normalize (unitProfile n) := by simpa [frontier] using hP
    refine ⟨[], rfl, ?_, ?_⟩
    · intro C hC; cases hC
    · simpa [SensitivityVariableWord.run] using heq.symm
  | succ k ih =>
    have hmem := FiniteDominance.prune_mem Below hP
    obtain ⟨Q, hQ, hPQ⟩ := List.mem_flatMap.mp hmem
    obtain ⟨C, hC, hCP⟩ := List.mem_map.mp hPQ
    obtain ⟨word, hlen, hadm, hrun⟩ := ih hQ
    refine ⟨word ++ [C.recipe], by simp [hlen], ?_, ?_⟩
    · intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact hadm D hD
      · have hD' : D = C.recipe := by simpa using hD
        subst D
        exact ⟨(mem_alphabet C).mp hC, fun i _ _ => (C.tol i).isLt⟩
    · rw [run_snoc, hrun]
      exact hCP

theorem frontier_covers (letters : List (Letter G.toleranceCount n))
    (hvalid : ∀ C ∈ letters, C.recipe.Valid) :
    ∃ P ∈ frontier G n letters.length,
      Below P (SensitivityVariableWord.run G (letters.map Letter.recipe) (unitProfile n)) := by
  induction letters using List.reverseRecOn with
  | nil =>
    refine ⟨normalize (unitProfile n), ?_, below_refl _⟩
    simp [frontier]
  | append_singleton letters C ih =>
    obtain ⟨P, hP, hbound⟩ := ih (fun D hD => hvalid D (by simp [hD]))
    have hC : C ∈ alphabet G.toleranceCount n := (mem_alphabet C).mpr (hvalid C (by simp))
    have hstep : SensitivityVariableWord.step G C.recipe P ∈ expand G (frontier G n letters.length) := by
      apply List.mem_flatMap.mpr
      exact ⟨P, hP, List.mem_map.mpr ⟨C, hC, rfl⟩⟩
    obtain ⟨Q, hQ, hQP⟩ := FiniteDominance.prune_cover Below
      below_refl (fun _ _ _ => below_trans) hstep
    refine ⟨Q, ?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton, frontier] using hQ
    · simp only [List.map_append, List.map_cons, List.map_nil, run_snoc]
      exact below_trans hQP (below_step C.recipe hbound)

theorem frontier_correctness (n k : ℕ) :
    succeeds G n k = true ↔
      ∃ word : List (Recipe n), word.length = k ∧ Crosses215 G word := by
  constructor
  · intro h
    obtain ⟨P, hP, hgap⟩ := List.any_eq_true.mp h
    have hgap' : height P ^ 43 < G.vertices ^ (20*k) := of_decide_eq_true hgap
    obtain ⟨word, hlen, hadm, hrun⟩ := frontier_sound hP
    refine ⟨word, hlen, ?_, hadm, ?_⟩
    · intro he
      have hk : k = 0 := by simpa [he] using hlen.symm
      have hheight : 2 ≤ height P := le_max_left _ _
      have hpower : 1 ≤ height P ^ 43 := Nat.one_le_pow 43 _ (by omega)
      simp only [hk, Nat.mul_zero, pow_zero] at hgap'
      omega
    · simpa only [hlen, hrun] using hgap'
  · rintro ⟨word, hlen, hcross⟩
    obtain ⟨letters, hlen', hvalid, hrun⟩ := encode_word word hcross.2.1
    obtain ⟨P, hP, hbound⟩ := frontier_covers letters hvalid
    apply List.any_eq_true.mpr
    refine ⟨P, ?_, ?_⟩
    · simpa only [hlen', hlen] using hP
    · apply decide_eq_true
      have hb := below_height hbound
      rw [hrun] at hb
      have hp : height P ^ 43 ≤ height (SensitivityVariableWord.run G word (unitProfile n)) ^ 43 := by gcongr
      simpa only [hlen] using hp.trans_lt hcross.2.2

end SensitivityVariableFrontier

theorem solution (G : SensitivityVariableWord.GraphData) (n k : ℕ) :
    SensitivityVariableFrontier.succeeds G n k = true ↔
      ∃ word : List (SensitivityProfileCycle.Recipe n), word.length = k ∧
        SensitivityVariableWord.Crosses215 G word :=
  SensitivityVariableFrontier.frontier_correctness (G := G) n k

#print axioms solution
