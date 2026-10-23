-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.twoCopyConversions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:44:40.765421+00:00
-- url     : https://prove2.me/submissions/38294cdd-a96d-414b-947c-b78fe92200fc

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal


namespace X7TwoCopy

open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

/-- Pushforward of a weight function `μ` on `Ω` along `X`. -/
def X7_push {n : ℕ} {Ω : Type} [Fintype Ω] (d : Fin n → ℕ) (μ : Ω → ℝ)
    (X : Ω → ClassicalBasis d) : CData n :=
  ⟨d, fun x => ∑ ω, if X ω = x then μ ω else 0⟩

def X7_Good {n : ℕ} {Ω : Type} [Fintype Ω] (d : Fin n → ℕ) (μ : Ω → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ (∀ ω, 0 ≤ μ ω) ∧ ∑ ω, μ ω = 1

lemma X7_push_valid {n : ℕ} {Ω : Type} [Fintype Ω] (d : Fin n → ℕ) (μ : Ω → ℝ)
    (X : Ω → ClassicalBasis d) (hG : X7_Good d μ) : IsValidClassicalData (X7_push d μ X) := by
  obtain ⟨hd, hμ0, hμ1⟩ := hG
  refine ⟨hd, fun x => Finset.sum_nonneg fun ω _ => ?_, ?_⟩
  · split_ifs <;> [exact hμ0 ω; exact le_rfl]
  · show ∑ x, ∑ ω, (if X ω = x then μ ω else 0) = 1
    rw [Finset.sum_comm]
    simpa [Finset.sum_ite_eq] using hμ1

lemma X7_leaf {n : ℕ} {Ω : Type} [Fintype Ω] (d : Fin n → ℕ) (μ : Ω → ℝ)
    (X : Ω → ClassicalBasis d) (hG : X7_Good d μ) (q : CData n) (hq : X7_push d μ X = q) :
    ExactSecretConversion (X7_push d μ X) q := by
  refine ⟨[(1, X7_push d μ X)], CLOPC.stop _ (X7_push_valid d μ X hG), ?_⟩
  intro z hz _
  simp only [List.mem_singleton] at hz
  subst hz; exact hq

theorem X7_step {n : ℕ} {Ω : Type} [Fintype Ω] (q : CData n) (d : Fin n → ℕ) (μ : Ω → ℝ)
    (X : Ω → ClassicalBasis d) (hG : X7_Good d μ)
    (party : Fin n) {k : ℕ} (α : Fin (d party) → Fin k) (w : Fin k → ℝ)
    (hwpos : ∀ j, 0 < w j)
    (hw : ∀ j, w j = ∑ ω, if α (X ω party) = j then μ ω else 0)
    (d' : Fin k → Fin n → ℕ) (hd' : ∀ j i, 0 < d' j i)
    (hdd : ∀ j i, i ≠ party → d' j i = d i)
    (f : (j : Fin k) → Fin (d party) → Fin (d' j party))
    (Y : (j : Fin k) → Ω → ClassicalBasis (d' j))
    (hY1 : ∀ j ω i, i ≠ party → (Y j ω i).val = (X ω i).val)
    (hY2 : ∀ j ω, Y j ω party = f j (X ω party))
    (μ' : Fin k → Ω → ℝ) (hμ' : ∀ j ω, μ' j ω * w j = if α (X ω party) = j then μ ω else 0)
    (hnext : ∀ j, X7_Good (d' j) (μ' j) →
      ExactSecretConversion (X7_push (d' j) (μ' j) (Y j)) q) :
    ExactSecretConversion (X7_push d μ X) q := by
  obtain ⟨hd, hμ0, hμ1⟩ := hG
  have hμ'0 : ∀ j ω, 0 ≤ μ' j ω := by
    intro j ω
    have h := hμ' j ω
    have : 0 ≤ μ' j ω * w j := by rw [h]; split_ifs <;> [exact hμ0 ω; exact le_rfl]
    exact nonneg_of_mul_nonneg_left this (hwpos j)
  have hμ'1 : ∀ j, ∑ ω, μ' j ω = 1 := by
    intro j
    have h : (∑ ω, μ' j ω) * w j = w j := by
      rw [Finset.sum_mul]; simp_rw [hμ' j]; exact (hw j).symm
    have := (hwpos j).ne'
    calc ∑ ω, μ' j ω = (∑ ω, μ' j ω) * w j / w j := by field_simp
      _ = 1 := by rw [h]; field_simp
  have hG' : ∀ j, X7_Good (d' j) (μ' j) := fun j => ⟨hd' j, hμ'0 j, hμ'1 j⟩
  have hkey : ∀ j ω (y : ClassicalBasis (d' j)), Y j ω = y ↔
      ((∀ i, i ≠ party → (X ω i).val = (y i).val) ∧ f j (X ω party) = y party) := by
    intro j ω y
    constructor
    · rintro rfl
      exact ⟨fun i hi => (hY1 j ω i hi).symm, (hY2 j ω).symm⟩
    · rintro ⟨h1, h2⟩
      funext i
      by_cases hi : i = party
      · subst hi; rw [hY2]; exact h2
      · exact Fin.ext ((hY1 j ω i hi).trans (h1 i hi))
  have hinst : CInstrument (X7_push d μ X) w (fun j => X7_push (d' j) (μ' j) (Y j)) := by
    refine ⟨X7_push_valid d μ X ⟨hd, hμ0, hμ1⟩, ⟨fun j => (hwpos j).le, ?_⟩,
      fun j => X7_push_valid _ _ _ (hG' j), party,
      fun j a (b : Fin (d' j party)) => if α a = j ∧ f j a = b then 1 else 0, ?_, ?_, ?_, ?_⟩
    · simp_rw [hw]
      rw [Finset.sum_comm]
      simpa [Finset.sum_ite_eq'] using hμ1
    · exact hdd
    · intro j a b; dsimp only; split_ifs <;> norm_num
    · intro a
      have : ∀ j, (∑ b, if α a = j ∧ f j a = b then (1:ℝ) else 0) = if α a = j then 1 else 0 := by
        intro j
        by_cases h : α a = j
        · simp [h]
        · simp [h]
      show (∑ j, ∑ b, if α a = j ∧ f j a = b then (1:ℝ) else 0) = 1
      rw [Finset.sum_congr rfl fun j _ => this j]
      simp
    · intro j (y : ClassicalBasis (d' j))
      show w j * (∑ ω, if Y j ω = y then μ' j ω else 0) =
        ∑ x : ClassicalBasis d, if ∀ i, i ≠ party → (x i).val = (y i).val then
          (∑ ω, if X ω = x then μ ω else 0) *
            (if α (x party) = j ∧ f j (x party) = y party then (1:ℝ) else 0) else 0
      have rhs : ∀ x : ClassicalBasis d,
          (if ∀ i, i ≠ party → (x i).val = (y i).val then
            (∑ ω, if X ω = x then μ ω else 0) *
              (if α (x party) = j ∧ f j (x party) = y party then (1:ℝ) else 0) else 0) =
          ∑ ω, if X ω = x then
            (if (∀ i, i ≠ party → (X ω i).val = (y i).val) ∧ α (X ω party) = j ∧
              f j (X ω party) = y party then μ ω else 0) else 0 := by
        intro x
        by_cases hx : ∀ i, i ≠ party → (x i).val = (y i).val
        · rw [if_pos hx, Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases hX : X ω = x
          · subst hX
            by_cases hc : α (X ω party) = j ∧ f j (X ω party) = y party
            · rw [if_pos hc, if_pos rfl, if_pos rfl, if_pos ⟨hx, hc⟩, mul_one]
            · rw [if_neg hc, if_pos rfl, if_pos rfl, if_neg (fun h => hc h.2), mul_zero]
          · rw [if_neg hX, if_neg hX, zero_mul]
        · rw [if_neg hx]
          refine (Finset.sum_eq_zero fun ω _ => ?_).symm
          by_cases hX : X ω = x
          · subst hX; rw [if_pos rfl, if_neg (fun h => hx h.1)]
          · rw [if_neg hX]
      rw [Finset.sum_congr rfl fun x _ => rhs x, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      have hm := hμ' j ω
      by_cases hY : Y j ω = y
      · rw [if_pos hY, mul_comm, hm]
        rw [hkey] at hY
        by_cases h3 : α (X ω party) = j
        · rw [if_pos h3, if_pos ⟨hY.1, h3, hY.2⟩]
        · simp [h3]
      · rw [if_neg hY, mul_zero]
        rw [hkey] at hY
        by_cases h1 : ∀ i, i ≠ party → (X ω i).val = (y i).val
        · have h2 : ¬ f j (X ω party) = y party := fun h => hY ⟨h1, h⟩
          simp [h2]
        · simp [h1]
  choose outs houts hgood using fun j => hnext j (hG' j)
  refine ⟨_, CLOPC.step _ k w _ hinst outs houts, ?_⟩
  intro z hz hpos
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hz
  obtain ⟨j, z', hz', rfl⟩ := hz
  exact hgood j z' hz' ((mul_pos_iff_of_pos_left (hwpos j)).mp hpos)

def X7_mk {n : ℕ} {Ω : Type} (d : Fin n → ℕ) (v : Ω → Fin n → ℕ) (hv : ∀ ω i, v ω i < d i) :
    Ω → ClassicalBasis d := fun ω i => ⟨v ω i, hv ω i⟩

def X7_upd {n : ℕ} {Ω : Type} (v : Ω → Fin n → ℕ) (party : Fin n) (F : ℕ → ℕ) :
    Ω → Fin n → ℕ := fun ω i => if i = party then F (v ω party) else v ω i

lemma X7_upd_lt {n : ℕ} {Ω : Type} {d : Fin n → ℕ} {v : Ω → Fin n → ℕ}
    (hv : ∀ ω i, v ω i < d i) (party : Fin n) {m : ℕ} {F : ℕ → ℕ} (hF : ∀ t, F t < m) :
    ∀ ω i, X7_upd v party F ω i < Function.update d party m i := by
  intro ω i
  unfold X7_upd
  by_cases h : i = party
  · subst h; simp [hF]
  · simp [h, hv]

theorem X7_stepU {n : ℕ} {Ω : Type} [Fintype Ω] (q : CData n) (d : Fin n → ℕ) (μ : Ω → ℝ)
    (v : Ω → Fin n → ℕ) (hv : ∀ ω i, v ω i < d i)
    (party : Fin n) {k : ℕ} (A : ℕ → Fin k) (w : Fin k → ℝ) (hwpos : ∀ j, 0 < w j)
    (hw : ∀ j, w j = ∑ ω, if A (v ω party) = j then μ ω else 0)
    (m : Fin k → ℕ) (hm : ∀ j, 0 < m j) (F : Fin k → ℕ → ℕ) (hF : ∀ j t, F j t < m j)
    (hnext : ∀ j, X7_Good (Function.update d party (m j))
        (fun ω => if A (v ω party) = j then μ ω / w j else 0) →
      ExactSecretConversion (X7_push (Function.update d party (m j))
        (fun ω => if A (v ω party) = j then μ ω / w j else 0)
        (X7_mk _ (X7_upd v party (F j)) (X7_upd_lt hv party (hF j)))) q)
    (hG : X7_Good d μ) :
    ExactSecretConversion (X7_push d μ (X7_mk d v hv)) q := by
  refine X7_step q d μ (X7_mk d v hv) hG party (fun a => A a.val) w hwpos hw
    (fun j => Function.update d party (m j)) ?_ ?_
    (fun j a => ⟨F j a.val, by simpa using hF j a.val⟩)
    (fun j => X7_mk _ (X7_upd v party (F j)) (X7_upd_lt hv party (hF j))) ?_ ?_
    (fun j ω => if A (v ω party) = j then μ ω / w j else 0) ?_ hnext
  · intro j i
    by_cases h : i = party
    · subst h; simp [hm]
    · simp [h, hG.1 i]
  · intro j i hi; simp [hi]
  · intro j ω i hi; simp [X7_mk, X7_upd, hi]
  · intro j ω; ext; simp [X7_mk, X7_upd]
  · intro j ω
    have := (hwpos j).ne'
    by_cases h : A (v ω party) = j
    · simp only [X7_mk, h, if_true]; field_simp
    · simp only [X7_mk, h, if_false, zero_mul]

theorem X7_private {n : ℕ} {Ω : Type} [Fintype Ω] (q : CData n) (d : Fin n → ℕ) (μ : Ω → ℝ)
    (v : Ω → Fin n → ℕ) (hv : ∀ ω i, v ω i < d i)
    (party : Fin n) (m : ℕ) (hm : 0 < m) (F : ℕ → ℕ) (hF : ∀ t, F t < m)
    (hnext : X7_Good (Function.update d party m) μ →
      ExactSecretConversion (X7_push (Function.update d party m) μ
        (X7_mk _ (X7_upd v party F) (X7_upd_lt hv party hF))) q)
    (hG : X7_Good d μ) :
    ExactSecretConversion (X7_push d μ (X7_mk d v hv)) q := by
  refine X7_step q d μ (X7_mk d v hv) hG party (k := 1) (fun _ => 0) (fun _ => 1)
    (fun _ => one_pos) ?_
    (fun _ => Function.update d party m) ?_ ?_
    (fun _ a => ⟨F a.val, by simpa using hF a.val⟩)
    (fun _ => X7_mk _ (X7_upd v party F) (X7_upd_lt hv party hF)) ?_ ?_
    (fun _ => μ) ?_ (fun _ h => hnext h)
  · intro j
    rw [Subsingleton.elim j 0]
    simp [hG.2.2]
  · intro j i
    by_cases h : i = party
    · subst h; simp [hm]
    · simp [h, hG.1 i]
  · intro j i hi; simp [hi]
  · intro j ω i hi; simp [X7_mk, X7_upd, hi]
  · intro j ω; ext; simp [X7_mk, X7_upd]
  · intro j ω
    rw [Subsingleton.elim j 0]
    simp

theorem X7_leafE {Ω : Type} [Fintype Ω] (k : Fin 5) (d : Fin 3 → ℕ) (hd : d = fun _ => 2)
    (μ : Ω → ℝ) (v : Ω → Fin 3 → ℕ) (hv : ∀ ω i, v ω i < d i) (hG : X7_Good d μ)
    (hprob : ∀ a b c : Fin 2, ∑ ω, (if v ω 0 = a.val ∧ v ω 1 = b.val ∧ v ω 2 = c.val
      then μ ω else 0) = (exampleLaw k).prob ![a, b, c]) :
    ExactSecretConversion (X7_push d μ (X7_mk d v hv)) (exampleLaw k) := by
  subst hd
  refine X7_leaf _ μ _ hG _ ?_
  unfold X7_push
  show (⟨fun _ => 2, _⟩ : CData 3) = ⟨fun _ => 2, (exampleLaw k).prob⟩
  congr 1
  funext x
  have hx : x = ![x 0, x 1, x 2] := by
    funext i; fin_cases i <;> rfl
  rw [hx, ← hprob]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  apply propext
  simp only [X7_mk, funext_iff, Fin.ext_iff, Fin.forall_fin_succ, Fin.isValue]
  simp

theorem X7_init {Ω : Type} [Fintype Ω] (k : Fin 5) (D : Fin 3 → ℕ)
    (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)) (μ0 : Ω → ℝ)
    (U : Ω → Fin 3 → Fin 2 → Fin 2)
    (H : ∀ u : Fin 3 → Fin 2 → Fin 2, ∏ j : Fin 2, (exampleLaw k).prob (fun i => u i j) =
      ∑ ω, if U ω = u then μ0 ω else 0) :
    (⟨D, fun x => ∏ j : Fin 2, (exampleLaw k).prob (fun i => (e i).symm (x i) j)⟩ : CData 3) =
      X7_push D μ0 (X7_mk D (fun ω i => (e i (U ω i)).val) (fun ω i => (e i (U ω i)).isLt)) := by
  unfold X7_push
  congr 1
  funext x
  rw [H (fun i => (e i).symm (x i))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    apply Fin.ext
    simp only [X7_mk]
    have : U ω i = (e i).symm (x i) := congrFun h i
    rw [this]; simp
  · intro h
    funext i
    have : (e i (U ω i)) = x i := by
      rw [← h]; rfl
    rw [← this]; simp

def X7_dec (k : Fin 5) (D : Fin 3 → ℕ)
    (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)) (i : Fin 3) (t : ℕ) :
    Fin 2 → Fin 2 :=
  if h : t < D i then (e i).symm ⟨t, h⟩ else fun _ => 0

@[simp] lemma X7_dec_e (k : Fin 5) (D : Fin 3 → ℕ)
    (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)) (i : Fin 3)
    (w : Fin 2 → Fin 2) : X7_dec k D e i (e i w).val = w := by
  unfold X7_dec
  split
  · simp
  · exact absurd (e i w).isLt ‹_›

lemma X7_Dpos (k : Fin 5) (D : Fin 3 → ℕ)
    (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)) (i : Fin 3) : 0 < D i :=
  Fin.pos (e i (fun _ => (0 : Fin 2)))

def X7_U1 (ω : Fin 2 × Fin 2) : Fin 3 → Fin 2 → Fin 2 :=
  ![![ω.1, ω.2], ![ω.1, ω.2], ![ω.1, ω.2]]

set_option maxHeartbeats 4000000 in
theorem X7_common_xor (D : Fin 3 → ℕ) (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)) :
    ExactSecretConversion
      (⟨D, fun x => ∏ j : Fin 2, (exampleLaw 3).prob (fun i => (e i).symm (x i) j)⟩ : CData 3)
      (exampleLaw 4) := by
  rw [X7_init 3 D e (fun _ : Fin 2 × Fin 2 => (1/4 : ℝ)) X7_U1 ?H]
  case H =>
    intro u
    obtain ⟨a,b,c,d,e,f,rfl⟩ : ∃ a b c d e f : Fin 2, u = ![![a,b],![c,d],![e,f]] :=
      ⟨u 0 0, u 0 1, u 1 0, u 1 1, u 2 0, u 2 1, by funext i j; fin_cases i <;> fin_cases j <;> rfl⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two, X7_U1, exampleLaw] <;> norm_num
  refine X7_private (Ω := Fin 2 × Fin 2) _ _ _ _ _ (0 : Fin 3) 2 (by norm_num)
    (fun t => (X7_dec 3 D e 0 t 0).val) (fun t => Fin.isLt _) ?_ ?_
  · intro hG1
    refine X7_private (Ω := Fin 2 × Fin 2) _ _ _ _ _ (1 : Fin 3) 2 (by norm_num)
      (fun t => (X7_dec 3 D e 1 t 1).val) (fun t => Fin.isLt _) ?_ hG1
    intro hG2
    refine X7_private (Ω := Fin 2 × Fin 2) _ _ _ _ _ (2 : Fin 3) 2 (by norm_num)
      (fun t => (X7_dec 3 D e 2 t 0 + X7_dec 3 D e 2 t 1).val) (fun t => Fin.isLt _) ?_ hG2
    intro hG3
    refine X7_leafE 4 _ ?_ _ _ _ hG3 ?_
    · funext i; fin_cases i <;> simp
    · intro a b cc
      fin_cases a <;> fin_cases b <;> fin_cases cc <;>
        simp [Fintype.sum_prod_type, Fin.sum_univ_two, X7_U1, X7_upd, exampleLaw] <;> norm_num
  · refine ⟨X7_Dpos 3 D e, fun _ => by norm_num, ?_⟩
    simp

def X7_U2 (ω : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Fin 3 → Fin 2 → Fin 2 :=
  ![![ω.1, ω.2.2.1], ![ω.2.1, ω.2.2.2], ![ω.1 + ω.2.1, ω.2.2.1 + ω.2.2.2]]

set_option maxHeartbeats 4000000 in
theorem X7_xor_common (D : Fin 3 → ℕ) (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)) :
    ExactSecretConversion
      (⟨D, fun x => ∏ j : Fin 2, (exampleLaw 4).prob (fun i => (e i).symm (x i) j)⟩ : CData 3)
      (exampleLaw 3) := by
  rw [X7_init 4 D e (fun _ : Fin 2 × Fin 2 × Fin 2 × Fin 2 => (1/16 : ℝ)) X7_U2 ?H]
  case H =>
    intro u
    obtain ⟨a,b,c,d,e,f,rfl⟩ : ∃ a b c d e f : Fin 2, u = ![![a,b],![c,d],![e,f]] :=
      ⟨u 0 0, u 0 1, u 1 0, u 1 1, u 2 0, u 2 1, by funext i j; fin_cases i <;> fin_cases j <;> rfl⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two, X7_U2, exampleLaw] <;> norm_num
  refine X7_stepU (Ω := Fin 2 × Fin 2 × Fin 2 × Fin 2) _ _ _ _ _ (2 : Fin 3) (fun t => X7_dec 4 D e 2 t 0) (fun _ => 1/2) (fun _ => by norm_num)
    ?_ (fun _ => 2) (fun _ => by norm_num) (fun _ t => (X7_dec 4 D e 2 t 1).val)
    (fun _ t => Fin.isLt _) ?_ ?_
  · intro c
    fin_cases c <;> simp [Fintype.sum_prod_type, Fin.sum_univ_two, X7_U2] <;> norm_num
  · intro c hG1
    refine X7_stepU (Ω := Fin 2 × Fin 2 × Fin 2 × Fin 2) _ _ _ _ _ (1 : Fin 3) (fun t => X7_dec 4 D e 1 t 0 + X7_dec 4 D e 1 t 1)
      (fun _ => 1/2) (fun _ => by norm_num)
      ?_ (fun _ => 2) (fun _ => by norm_num) (fun _ t => (X7_dec 4 D e 1 t 1).val)
      (fun _ t => Fin.isLt _) ?_ hG1
    · intro mm
      fin_cases c <;> fin_cases mm <;>
        simp [Fintype.sum_prod_type, Fin.sum_univ_two, X7_U2, X7_upd] <;> norm_num
    · intro mm hG2
      refine X7_stepU (Ω := Fin 2 × Fin 2 × Fin 2 × Fin 2) _ _ _ _ _ (0 : Fin 3) (fun t => X7_dec 4 D e 0 t 1)
        (fun _ => 1/2) (fun _ => by norm_num)
        ?_ (fun _ => 2) (fun _ => by norm_num)
        (fun _ t => (X7_dec 4 D e 0 t 0 + c + mm).val)
        (fun _ t => Fin.isLt _) ?_ hG2
      · intro r
        fin_cases c <;> fin_cases mm <;> fin_cases r <;>
          simp [Fintype.sum_prod_type, Fin.sum_univ_two, X7_U2, X7_upd] <;> norm_num
      · intro r hG3
        refine X7_private (Ω := Fin 2 × Fin 2 × Fin 2 × Fin 2) _ _ _ _ _ (2 : Fin 3) 2 (by norm_num) (fun t => (t + r.val) % 2)
          (fun t => Nat.mod_lt _ (by norm_num)) ?_ hG3
        intro hG4
        refine X7_leafE 3 _ ?_ _ _ _ hG4 ?_
        · funext i; fin_cases i <;> simp
        · intro a b cc
          fin_cases c <;> fin_cases mm <;> fin_cases r <;> fin_cases a <;> fin_cases b <;>
            fin_cases cc <;>
            simp [Fintype.sum_prod_type, Fin.sum_univ_two, X7_U2, X7_upd, exampleLaw] <;> norm_num
  · refine ⟨X7_Dpos 4 D e, fun _ => by norm_num, ?_⟩
    simp

end X7TwoCopy

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Renew46.P37 X7TwoCopy in
theorem solution :
    ExactSecretConversion (cCopies (exampleLaw 3) 2) (exampleLaw 4) ∧
    ExactSecretConversion (cCopies (exampleLaw 4) 2) (exampleLaw 3) := by
  obtain ⟨D, e, hc⟩ : ∃ (D : Fin 3 → ℕ) (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)),
      cCopies (exampleLaw 3) 2 =
        ⟨D, fun x => ∏ j : Fin 2, (exampleLaw 3).prob (fun i => (e i).symm (x i) j)⟩ :=
    ⟨_, fun i => Fintype.equivFin _, rfl⟩
  obtain ⟨D', e', hc'⟩ : ∃ (D : Fin 3 → ℕ) (e : ∀ i, (Fin 2 → Fin 2) ≃ Fin (D i)),
      cCopies (exampleLaw 4) 2 =
        ⟨D, fun x => ∏ j : Fin 2, (exampleLaw 4).prob (fun i => (e i).symm (x i) j)⟩ :=
    ⟨_, fun i => Fintype.equivFin _, rfl⟩
  rw [hc, hc']
  exact ⟨X7_common_xor D e, X7_xor_common D' e'⟩

end
