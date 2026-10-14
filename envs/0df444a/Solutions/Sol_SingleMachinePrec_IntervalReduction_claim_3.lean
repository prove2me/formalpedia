-- Prove2me | solution 1 for SingleMachinePrec.IntervalReduction.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:39:09.931549+00:00
-- url     : https://prove2.me/submissions/1f64a9b6-d31e-4b75-85f0-1e4ce0535a92

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance



namespace SingleMachinePrec.IntervalReduction

variable {N : ℕ} {G : SimpleGraph (Fin N)}

lemma ceil_nat_cast_sub_half (n : ℕ) (hn : 1 ≤ n) : ⌈((n : ℝ) - 1 / 2)⌉ = (n : ℤ) := by
  rw [Int.ceil_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

lemma ceil_right (L : TreeLayout G) (x : Job L) :
    ⌈right L x⌉ = match x with
      | .s0 => 0
      | .s j => (num j : ℤ)
      | .m i => ((N + num i : ℕ) : ℤ)
      | .e i => ((N + num i + 1 : ℕ) : ℤ)
      | .b q => (num q.1.2 : ℤ) := by
  cases x with
  | s0 => simp [right]
  | s j => simp only [right]; exact Int.ceil_natCast _
  | m i =>
    simp only [right]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i)]; push_cast; rfl
  | e i =>
    simp only [right]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i + 1)]; push_cast; rfl
  | b q =>
    simp only [right]
    exact ceil_nat_cast_sub_half _ (by simp [num])

lemma ceil_left (L : TreeLayout G) (x : Job L) :
    ⌈left L x⌉ = match x with
      | .s0 => -1
      | .s j => (parNum L j : ℤ)
      | .m i => (num i : ℤ)
      | .e i => ((N + num i : ℕ) : ℤ)
      | .b q => (num q.1.1 : ℤ) := by
  cases x with
  | s0 => simp only [left]; exact Int.ceil_eq_iff.mpr (by norm_num)
  | s j => simp only [left]; exact Int.ceil_natCast _
  | m i =>
    simp only [left]
    exact ceil_nat_cast_sub_half _ (by simp [num])
  | e i =>
    simp only [left]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i)]; push_cast; rfl
  | b q => simp only [left]; exact Int.ceil_natCast _

lemma procTime_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    procTime L k x = 0 ∨ procTime L k x = k ^ (-⌈right L x⌉) := by
  have hk0 : k ≠ 0 := by positivity
  rw [ceil_right]
  cases x with
  | s0 => right; simp [procTime]
  | s j => right; simp [procTime, zpow_neg]
  | m i => right; simp only [procTime]; rw [one_div, ← zpow_natCast, ← zpow_neg]
  | e i => left; simp [procTime]
  | b q => right; simp [procTime, zpow_neg]

lemma weight_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    weight L k x = 0 ∨ weight L k x = k ^ ⌈left L x⌉ := by
  have hk0 : k ≠ 0 := by positivity
  rw [ceil_left]
  cases x with
  | s0 => left; simp [weight]
  | s j => right; simp [weight]
  | m i => right; simp [weight]
  | e i => right; simp only [weight]; exact (zpow_natCast _ _).symm
  | b q => right; simp [weight]

lemma procTime_le (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    procTime L k x ≤ 1 / k ^ ⌈right L x⌉ := by
  have hk0 : 0 < k := by positivity
  rcases procTime_cases L k hk x with h | h
  · rw [h]; positivity
  · rw [h, zpow_neg, one_div]

lemma weight_le (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    weight L k x ≤ k ^ ⌈left L x⌉ := by
  have hk0 : 0 < k := by positivity
  rcases weight_cases L k hk x with h | h
  · rw [h]; positivity
  · rw [h]

lemma prod_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L) :
    procTime L k x * weight L k y = 0 ∨
      procTime L k x * weight L k y = k ^ (⌈left L y⌉ - ⌈right L x⌉) := by
  have hk0 : k ≠ 0 := by positivity
  rcases procTime_cases L k hk x with h | h
  · left; rw [h]; simp
  rcases weight_cases L k hk y with h' | h'
  · left; rw [h']; simp
  · right; rw [h, h', ← zpow_add₀ hk0]; congr 1; ring

lemma prod_le_one_of (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : left L y ≤ right L x) :
    procTime L k x * weight L k y ≤ 1 := by
  have hle : ⌈left L y⌉ ≤ ⌈right L x⌉ := Int.ceil_le_ceil h
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0]; norm_num
  · rw [h0]; exact zpow_le_one_of_nonpos₀ hk.le (by omega)

lemma prod_le_inv_of (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : left L y ≤ right L x) (h' : ⌈left L y⌉ ≠ ⌈right L x⌉) :
    procTime L k x * weight L k y ≤ 1 / k := by
  have hk0 : 0 < k := by positivity
  have hle : ⌈left L y⌉ ≤ ⌈right L x⌉ := Int.ceil_le_ceil h
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0]; positivity
  · rw [h0, one_div, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hk.le (by omega)

lemma prod_eq_one_iff (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : procTime L k x * weight L k y = 1) : ⌈left L y⌉ = ⌈right L x⌉ := by
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0] at h; norm_num at h
  · rw [h0] at h
    have := (zpow_eq_one_iff_right₀ (by linarith) hk.ne').mp h
    omega


lemma parNum_eq_zero (L : TreeLayout G) (j : Fin N) : parNum L j = 0 ↔ L.par j = none := by
  unfold parNum
  cases h : L.par j <;> simp

lemma parNum_eq_num (L : TreeLayout G) (j i : Fin N) : parNum L j = num i ↔ L.par j = some i := by
  unfold parNum num
  cases h : L.par j with
  | none => simp
  | some i' => simp [Fin.ext_iff]

lemma parNum_lt (L : TreeLayout G) (j : Fin N) : parNum L j < N := by
  unfold parNum
  cases h : L.par j with
  | none => simp; exact lt_of_le_of_lt (Nat.zero_le _) j.2
  | some i' =>
    have := L.par_lt j i' h
    have h2 : i'.val < j.val := this
    have := j.2
    simp; omega

lemma num_le (i : Fin N) : num i ≤ N := by unfold num; have := i.2; omega
lemma num_pos (i : Fin N) : 1 ≤ num i := by unfold num; omega
lemma num_inj {i j : Fin N} : num i = num j ↔ i = j := by
  unfold num; simp [Fin.ext_iff]

lemma InD_key (L : TreeLayout G) (x y : Job L) (hinc : Incomparable (prec L) x y)
    (hceil : ⌈left L y⌉ = ⌈right L x⌉) (hx : ∀ i, x ≠ .e i) (hy : y ≠ .s0) : InD L x y := by
  rw [ceil_left, ceil_right] at hceil
  cases x with
  | s0 =>
    cases y with
    | s0 => exact absurd rfl hy
    | s j => simp only [InD]; simp at hceil; exact (parNum_eq_zero L j).mp (by omega)
    | m i => simp at hceil; have := num_pos i; omega
    | e i => simp at hceil; have := num_pos i; omega
    | b q => simp at hceil; have := num_pos q.1.1; omega
  | s j =>
    have h1 := num_le j
    cases y with
    | s0 => exact absurd rfl hy
    | s j' => simp only [InD]; simp at hceil; exact (parNum_eq_num L j' j).mp (by omega)
    | m i => simp at hceil; simp only [InD]; exact (num_inj.mp (by omega)).symm
    | e i => simp at hceil; have := num_pos i; omega
    | b q => simp at hceil; simp only [InD]; exact num_inj.mp (by omega)
  | m i =>
    have h1 := num_le i
    cases y with
    | s0 => exact absurd rfl hy
    | s j' => simp at hceil; have := parNum_lt L j'; omega
    | m i' => simp at hceil; have := num_le i'; have := num_pos i; omega
    | e i' => simp at hceil; simp only [InD]; exact (num_inj.mp (by omega))
    | b q => simp at hceil; have := num_le q.1.1; have := num_pos i; omega
  | e i => exact absurd rfl (hx i)
  | b q =>
    have h1 := num_le q.1.2
    have h2 : (1:ℕ) ≤ num q.1.2 := num_pos _
    cases y with
    | s0 => exact absurd rfl hy
    | s j' =>
      simp at hceil
      exfalso; apply hinc.1; right
      simp only [right, left]
      have : (parNum L j' : ℝ) = num q.1.2 := by exact_mod_cast hceil
      rw [this]; linarith
    | m i' => simp at hceil; simp only [InD]; exact num_inj.mp (by omega)
    | e i' => simp at hceil; have := num_pos i'; omega
    | b q' =>
      simp at hceil
      exfalso; apply hinc.1; right
      simp only [right, left]
      have : (num q'.1.1 : ℝ) = num q.1.2 := by exact_mod_cast hceil
      rw [this]; linarith

lemma claim2_core (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (hxy : Incomparable (prec L) x y) :
    (InD L x y → procTime L k x * weight L k y = 1) ∧
    (¬ InD L x y → procTime L k x * weight L k y ≤ 1 / k) := by
  have hk0 : k ≠ 0 := by positivity
  constructor
  · intro h
    cases x <;> cases y <;> simp only [InD] at h <;> try contradiction
    · simp [procTime, weight, (parNum_eq_zero L _).mpr h]
    · have := (parNum_eq_num L _ _).mpr h
      simp only [procTime, weight, this]
      field_simp
    all_goals (subst h; simp only [procTime, weight]; field_simp)
  · intro h
    by_cases hx : ∃ i, x = .e i
    · obtain ⟨i, rfl⟩ := hx
      simp [procTime]; positivity
    by_cases hy : y = .s0
    · subst hy; simp [weight]; positivity
    push_neg at hx
    have hle : left L y ≤ right L x := not_lt.mp (fun h => hxy.1 (Or.inr h))
    refine prod_le_inv_of L k hk x y hle ?_
    intro he
    exact h (InD_key L x y hxy he hx hy)

lemma parNum_le_val (L : TreeLayout G) (j : Fin N) : parNum L j ≤ j.val := by
  unfold parNum
  cases h : L.par j with
  | none => simp
  | some i' =>
    have h2 : i'.val < j.val := L.par_lt j i' h
    simp; omega

lemma par_iff (L : TreeLayout G) (j i : Fin N) : L.par j = some i ↔ parNum L j = i.val + 1 :=
  (parNum_eq_num L j i).symm

def l2 (L : TreeLayout G) : Job L → ℤ
  | .s0 => -2
  | .s j => 2 * (parNum L j : ℤ)
  | .m i => 2 * ((i.val : ℤ) + 1) - 1
  | .e i => 2 * ((N : ℤ) + (i.val + 1))
  | .b q => 2 * ((q.1.1.val : ℤ) + 1)

def r2 (L : TreeLayout G) : Job L → ℤ
  | .s0 => 0
  | .s j => 2 * ((j.val : ℤ) + 1)
  | .m i => 2 * ((N : ℤ) + (i.val + 1))
  | .e i => 2 * ((N : ℤ) + (i.val + 1)) + 2
  | .b q => 2 * ((q.1.2.val : ℤ) + 1) - 1

lemma left_eq (L : TreeLayout G) (x : Job L) : left L x = (l2 L x : ℝ) / 2 := by
  cases x <;> simp [left, l2, num] <;> ring

lemma right_eq (L : TreeLayout G) (x : Job L) : right L x = (r2 L x : ℝ) / 2 := by
  cases x <;> simp [right, r2, num] <;> ring

lemma le_iff (L : TreeLayout G) (x y : Job L) : x ≤ y ↔ x = y ∨ r2 L x < l2 L y := by
  show (x = y ∨ right L x < left L y) ↔ _
  rw [right_eq, left_eq, div_lt_div_iff_of_pos_right (by norm_num)]
  simp

lemma vcg_adj (L : TreeLayout G) (u v : IncPair (prec L)) :
    (vertexCoverGraph (prec L)).Adj u v ↔
      u.1 ≠ v.1 ∧ u.1.1 ≤ v.1.2 ∧ v.1.1 ≤ u.1.2 := by
  show (u ≠ v ∧ (csRule (prec L) u v ∨ csRule (prec L) v u)) ↔ _
  have hne : u ≠ v ↔ u.1 ≠ v.1 :=
    ⟨fun h h' => h (Subtype.ext h'), fun h h' => h (congrArg Subtype.val h')⟩
  rw [hne]
  have hp : ∀ x y : Job L, prec L x y ↔ x ≤ y := fun _ _ => Iff.rfl
  have h1 : ∀ u v : IncPair (prec L), csRule (prec L) u v ↔ u.1.1 ≤ v.1.2 ∧ v.1.1 ≤ u.1.2 := by
    intro u v
    unfold csRule
    simp only [hp]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h2.le, h1.symm.le⟩
      · exact ⟨h2, h1.symm.le⟩
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact Or.inr (Or.inr ⟨h1, h2⟩)
  rw [h1, h1]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.2, h'.1⟩
  · rintro ⟨h, h'⟩; exact ⟨h, Or.inl h'⟩


def parJob (L : TreeLayout G) (j : Fin N) : Job L :=
  match L.par j with
  | none => .s0
  | some i => .s i

lemma parJob_eq_s (L : TreeLayout G) (j i : Fin N) : parJob L j = .s i ↔ L.par j = some i := by
  unfold parJob
  cases h : L.par j <;> simp

lemma parJob_ne_s0 (L : TreeLayout G) (j : Fin N) : parJob L j = .s0 ↔ L.par j = none := by
  unfold parJob
  cases h : L.par j <;> simp

lemma parJob_ne_m (L : TreeLayout G) (j i : Fin N) : parJob L j ≠ .m i := by
  unfold parJob
  cases h : L.par j <;> simp
lemma parJob_ne_e (L : TreeLayout G) (j i : Fin N) : parJob L j ≠ .e i := by
  unfold parJob
  cases h : L.par j <;> simp
lemma parJob_ne_b (L : TreeLayout G) (j : Fin N) (q : NonTreeEdge L) : parJob L j ≠ .b q := by
  unfold parJob
  cases h : L.par j <;> simp

lemma r2_parJob (L : TreeLayout G) (j : Fin N) : r2 L (parJob L j) = 2 * (parNum L j : ℤ) := by
  unfold parJob parNum
  cases h : L.par j <;> simp [r2]

lemma l2_parJob_le (L : TreeLayout G) (j : Fin N) : l2 L (parJob L j) ≤ 2 * (j.val : ℤ) := by
  unfold parJob
  cases h : L.par j with
  | none => simp [l2]; omega
  | some i =>
    have h2 : i.val < j.val := L.par_lt j i h
    have := parNum_le_val L i
    simp only [l2]; omega

def pairOf (L : TreeLayout G) : GPVertex L → Job L × Job L
  | .v j => (parJob L j, .s j)
  | .u1 i => (.s i, .m i)
  | .u2 i => (.m i, .e i)
  | .e1 q => (.s q.1.1, .b q)
  | .e2 q => (.b q, .m q.1.2)

lemma nte_eq (L : TreeLayout G) (q q' : NonTreeEdge L) :
    q = q' ↔ q.1.1.val = q'.1.1.val ∧ q.1.2.val = q'.1.2.val := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)

lemma pj_and (L : TreeLayout G) (i j : Fin N) : (parJob L i = parJob L j ∧ i = j) ↔ i = j :=
  ⟨fun h => h.2, fun h => ⟨by rw [h], h⟩⟩

lemma pairOf_adj (L : TreeLayout G) (x y : GPVertex L) :
    (GPrime L).Adj x y ↔
      pairOf L x ≠ pairOf L y ∧ (pairOf L x).1 ≤ (pairOf L y).2 ∧ (pairOf L y).1 ≤ (pairOf L x).2 := by
  rw [GPrime, SimpleGraph.fromRel_adj]
  rcases x with i | i | i | q | q <;>
  rcases y with j | j | j | q' | q' <;>
  simp only [gpRel, pairOf, ne_eq, Prod.mk.injEq, le_iff, GPVertex.v.injEq, GPVertex.u1.injEq, GPVertex.u2.injEq, GPVertex.e1.injEq, GPVertex.e2.injEq, parJob_eq_s, par_iff, r2_parJob, Job.s.injEq, Job.m.injEq, Job.e.injEq, Job.b.injEq, reduceCtorEq, false_or, or_false, and_false, false_and, not_false_eq_true, true_and, and_true, parJob_ne_m, parJob_ne_e, parJob_ne_b, pj_and] <;>
  simp only [r2, l2, nte_eq, Fin.ext_iff, false_iff, iff_false] <;>
  (try have := parNum_le_val L i) <;> (try have := parNum_le_val L j) <;>
  (try have := Fin.lt_def.mp q.2.1) <;> (try have := Fin.lt_def.mp q'.2.1) <;>
  (try have := parNum_le_val L q.1.1) <;> (try have := parNum_le_val L q'.1.1) <;>
  (try have := parNum_le_val L q.1.2) <;> (try have := parNum_le_val L q'.1.2) <;>
  (try have := i.2) <;> (try have := j.2) <;> (try have := q.1.1.2) <;> (try have := q.1.2.2) <;>
  (try have := q'.1.1.2) <;> (try have := q'.1.2.2)
  all_goals omega


lemma s_eq_parJob (L : TreeLayout G) (j i : Fin N) : Job.s i = parJob L j ↔ L.par j = some i := by
  rw [eq_comm]; exact parJob_eq_s L j i

lemma pairOf_inc (L : TreeLayout G) (x : GPVertex L) :
    Incomparable (prec L) (pairOf L x).1 (pairOf L x).2 := by
  unfold Incomparable prec
  rcases x with i | i | i | q | q <;>
  simp only [pairOf, le_iff, parJob_eq_s, s_eq_parJob, par_iff, r2_parJob, Job.s.injEq, Job.m.injEq, Job.e.injEq,
    Job.b.injEq, reduceCtorEq, false_or, or_false, parJob_ne_m, parJob_ne_e, parJob_ne_b, not_or] <;>
  (try have h6 := l2_parJob_le L i) <;> (try generalize l2 L (parJob L i) = t at h6 ⊢) <;>
  simp only [r2, l2, Fin.ext_iff] <;>
  (try have := parNum_le_val L i) <;>
  (try have := Fin.lt_def.mp q.2.1) <;>
  (try have := i.2) <;> (try have := q.1.1.2) <;> (try have := q.1.2.2) <;>
  (try have := parNum_le_val L q.1.1) <;> (try have := parNum_le_val L q.1.2) <;>
  (try have h5 := L.par_lt i) <;>
  all_goals omega


lemma pairOf_inD (L : TreeLayout G) (x : GPVertex L) :
    InD L (pairOf L x).1 (pairOf L x).2 := by
  rcases x with j | i | i | q | q
  · cases h : L.par j <;> simp [pairOf, parJob, InD, h]
  · simp [pairOf, InD]
  · simp [pairOf, InD]
  · simp [pairOf, InD]
  · simp [pairOf, InD]

lemma pairOf_inj (L : TreeLayout G) : Function.Injective (pairOf L) := by
  intro x y h
  rcases x with i | i | i | q | q <;> rcases y with j | j | j | q' | q' <;>
    simp [pairOf] at h ⊢ <;> try (first | exact h | exact h.2 | exact h.1)

def Fmap (L : TreeLayout G) (x : GPVertex L) : {u : IncPair (prec L) | InD L u.1.1 u.1.2} :=
  ⟨⟨pairOf L x, pairOf_inc L x⟩, pairOf_inD L x⟩

lemma Fmap_surj (L : TreeLayout G) : Function.Surjective (Fmap L) := by
  rintro ⟨⟨⟨a, b⟩, hinc⟩, hD⟩
  have hD' : InD L a b := hD
  cases a <;> cases b <;> simp only [InD] at hD' <;> try contradiction
  · rename_i j
    refine ⟨.v j, Subtype.ext (Subtype.ext ?_)⟩
    show pairOf L (.v j) = (Job.s0, Job.s j)
    simp [pairOf, (parJob_ne_s0 L _).mpr hD']
  · rename_i i j
    refine ⟨.v j, Subtype.ext (Subtype.ext ?_)⟩
    show pairOf L (.v j) = (Job.s i, Job.s j)
    simp [pairOf, (parJob_eq_s L _ _).mpr hD']
  · subst hD'
    exact ⟨.u1 _, rfl⟩
  · subst hD'
    exact ⟨.e1 _, rfl⟩
  · subst hD'
    exact ⟨.u2 _, rfl⟩
  · subst hD'
    exact ⟨.e2 _, rfl⟩

noncomputable def isoG (L : TreeLayout G) : GPrime L ≃g GIprime L where
  toEquiv := Equiv.ofBijective (Fmap L)
    ⟨fun x y h => pairOf_inj L (congrArg (fun u => u.1.1) h), Fmap_surj L⟩
  map_rel_iff' := by
    intro x y
    show (vertexCoverGraph (prec L)).Adj (Fmap L x).1 (Fmap L y).1 ↔ _
    rw [vcg_adj]
    exact (pairOf_adj L x y).symm

theorem claim3_core {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    Nonempty (GIprime L ≃g GPrime L) := ⟨(isoG L).symm⟩

end SingleMachinePrec.IntervalReduction

open SingleMachinePrec.IntervalReduction


theorem solution {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    Nonempty (GIprime L ≃g GPrime L) := by
  exact claim3_core L
