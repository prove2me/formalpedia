-- Prove2me | solution 1 for Timetabling85.ClassTeacher.prop_2_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-13T10:38:10.159626+00:00
-- url     : https://prove2.me/submissions/81428e91-5f62-4f92-8268-f5262cc98c85

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems
import Theorems.Thm_Timetabling85_ClassTeacher_prop_2_1

namespace Timetabling85.ClassTeacher

abbrev ClassEdges {m n : ℕ} (R : Fin m → Fin n → ℕ) (i : Fin m) :=
  Σ j : Fin n, Fin (R i j)

abbrev TeacherEdges {m n : ℕ} (R : Fin m → Fin n → ℕ) (j : Fin n) :=
  Σ i : Fin m, Fin (R i j)

abbrev LectureEdges {m n : ℕ} (R : Fin m → Fin n → ℕ) :=
  Σ i : Fin m, ClassEdges R i

abbrev PairEdges {m n : ℕ} (R : Fin m → Fin n → ℕ) (i : Fin m) (j : Fin n) :=
  {e : LectureEdges R // e.1 = i ∧ e.2.1 = j}

abbrev ClassClones {m : ℕ} (a : Fin m → ℕ) :=
  Σ i : Fin m, Fin (a i)

abbrev TeacherClones {n : ℕ} (b : Fin n → ℕ) :=
  Σ j : Fin n, Fin (b j)

theorem card_classEdges {m n : ℕ} (R : Fin m → Fin n → ℕ) (i : Fin m) :
    Fintype.card (ClassEdges R i) = rowSum R i := by
  classical
  simp [ClassEdges, rowSum]

theorem card_teacherEdges {m n : ℕ} (R : Fin m → Fin n → ℕ) (j : Fin n) :
    Fintype.card (TeacherEdges R j) = colSum R j := by
  classical
  simp [TeacherEdges, colSum]

noncomputable def pairEdgesEquiv {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (i : Fin m) (j : Fin n) : Fin (R i j) ≃ PairEdges R i j where
  toFun k := ⟨⟨i, ⟨j, k⟩⟩, rfl, rfl⟩
  invFun e := Fin.cast (congrArg₂ R e.2.1 e.2.2) e.1.2.2
  left_inv k := by rfl
  right_inv e := by
    rcases e with ⟨⟨i', ⟨j', k⟩⟩, ⟨hi, hj⟩⟩
    cases hi
    cases hj
    rfl

noncomputable def classSlotEmbedding {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (p : ℕ) (hrow : ∀ i, rowSum R i ≤ p * a i) (i : Fin m) :
    ClassEdges R i ↪ Fin (a i) × Fin p := by
  classical
  have hcard : Fintype.card (ClassEdges R i) ≤ a i * p := by
    rw [card_classEdges]
    simpa [Nat.mul_comm] using hrow i
  exact (Fintype.equivFin (ClassEdges R i)).toEmbedding.trans
    ((Fin.castLEEmb hcard).trans finProdFinEquiv.symm.toEmbedding)

noncomputable def teacherSlotEmbedding {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (b : Fin n → ℕ) (p : ℕ) (hcol : ∀ j, colSum R j ≤ p * b j) (j : Fin n) :
    TeacherEdges R j ↪ Fin (b j) × Fin p := by
  classical
  have hcard : Fintype.card (TeacherEdges R j) ≤ b j * p := by
    rw [card_teacherEdges]
    simpa [Nat.mul_comm] using hcol j
  exact (Fintype.equivFin (TeacherEdges R j)).toEmbedding.trans
    ((Fin.castLEEmb hcard).trans finProdFinEquiv.symm.toEmbedding)

noncomputable def pairCloneMap {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (i : Fin m) (j : Fin n) (k : Fin (R i j)) : Fin (a i) × Fin (b j) :=
  ((classSlotEmbedding R a p hrow i ⟨j, k⟩).1,
    (teacherSlotEmbedding R b p hcol j ⟨i, k⟩).1)

abbrev pairCloneFiber {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (i : Fin m) (j : Fin n) (ci : Fin (a i)) (tj : Fin (b j)) :=
  {k : Fin (R i j) // pairCloneMap R a b p hrow hcol i j k = (ci, tj)}

noncomputable instance pairCloneFiberFintype {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (i : Fin m) (j : Fin n) (ci : Fin (a i)) (tj : Fin (b j)) :
    Fintype (pairCloneFiber R a b p hrow hcol i j ci tj) := Fintype.ofFinite _

noncomputable def pairClonePartitionEquiv {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (i : Fin m) (j : Fin n) :
    Fin (R i j) ≃ Σ ci : Fin (a i), Σ tj : Fin (b j),
      pairCloneFiber R a b p hrow hcol i j ci tj where
  toFun k := ⟨(pairCloneMap R a b p hrow hcol i j k).1,
    (pairCloneMap R a b p hrow hcol i j k).2, ⟨k, rfl⟩⟩
  invFun z := z.2.2.1
  left_inv k := by rfl
  right_inv z := by
    rcases z with ⟨ci, tj, ⟨k, h⟩⟩
    simp only [pairCloneMap, Prod.mk.injEq] at h
    cases h.1
    cases h.2
    rfl

theorem pairCloneFiber_card_sum {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (i : Fin m) (j : Fin n) :
    (∑ ci : Fin (a i), ∑ tj : Fin (b j),
      Fintype.card (pairCloneFiber R a b p hrow hcol i j ci tj)) = R i j := by
  classical
  calc
    (∑ ci : Fin (a i), ∑ tj : Fin (b j),
        Fintype.card (pairCloneFiber R a b p hrow hcol i j ci tj)) =
        Fintype.card (Σ ci : Fin (a i), Σ tj : Fin (b j),
          pairCloneFiber R a b p hrow hcol i j ci tj) := by
            simp only [Fintype.card_sigma]
    _ = Fintype.card (Fin (R i j)) :=
          Fintype.card_congr (pairClonePartitionEquiv R a b p hrow hcol i j).symm
    _ = R i j := Fintype.card_fin _

noncomputable def globalClassSlotEmbedding {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (p : ℕ) (hrow : ∀ i, rowSum R i ≤ p * a i) :
    LectureEdges R ↪ Σ i : Fin m, Fin (a i) × Fin p where
  toFun e := ⟨e.1, classSlotEmbedding R a p hrow e.1 e.2⟩
  inj' := by
    intro e₁ e₂ h
    rcases e₁ with ⟨i₁, e₁⟩
    rcases e₂ with ⟨i₂, e₂⟩
    change (⟨i₁, classSlotEmbedding R a p hrow i₁ e₁⟩ :
      Σ i : Fin m, Fin (a i) × Fin p) =
      ⟨i₂, classSlotEmbedding R a p hrow i₂ e₂⟩ at h
    rcases Sigma.mk.inj_iff.mp h with ⟨hi, hs⟩
    subst i₂
    have hp : classSlotEmbedding R a p hrow i₁ e₁ =
        classSlotEmbedding R a p hrow i₁ e₂ := eq_of_heq hs
    have he : e₁ = e₂ := (classSlotEmbedding R a p hrow i₁).injective hp
    cases he
    rfl

noncomputable def globalTeacherSlotEmbedding {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (b : Fin n → ℕ) (p : ℕ) (hcol : ∀ j, colSum R j ≤ p * b j) :
    LectureEdges R ↪ Σ j : Fin n, Fin (b j) × Fin p where
  toFun e := ⟨e.2.1, teacherSlotEmbedding R b p hcol e.2.1 ⟨e.1, e.2.2⟩⟩
  inj' := by
    intro e₁ e₂ h
    rcases e₁ with ⟨i₁, ⟨j₁, k₁⟩⟩
    rcases e₂ with ⟨i₂, ⟨j₂, k₂⟩⟩
    change (⟨j₁, teacherSlotEmbedding R b p hcol j₁ ⟨i₁, k₁⟩⟩ :
      Σ j : Fin n, Fin (b j) × Fin p) =
      ⟨j₂, teacherSlotEmbedding R b p hcol j₂ ⟨i₂, k₂⟩⟩ at h
    rcases Sigma.mk.inj_iff.mp h with ⟨hj, hs⟩
    subst j₂
    have hp : teacherSlotEmbedding R b p hcol j₁ ⟨i₁, k₁⟩ =
        teacherSlotEmbedding R b p hcol j₁ ⟨i₂, k₂⟩ := eq_of_heq hs
    have hedge : (⟨i₁, k₁⟩ : TeacherEdges R j₁) = ⟨i₂, k₂⟩ :=
      (teacherSlotEmbedding R b p hcol j₁).injective hp
    cases hedge
    rfl

noncomputable def classCloneOf {m n : ℕ} (R : Fin m → Fin n → ℕ) (a : Fin m → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (e : LectureEdges R) : ClassClones a :=
  ⟨e.1, (globalClassSlotEmbedding R a p hrow e).2.1⟩

noncomputable def teacherCloneOf {m n : ℕ} (R : Fin m → Fin n → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hcol : ∀ j, colSum R j ≤ p * b j) (e : LectureEdges R) : TeacherClones b :=
  ⟨e.2.1, (globalTeacherSlotEmbedding R b p hcol e).2.1⟩

noncomputable def expandedRequirements {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (c : ClassClones a) (t : TeacherClones b) : ℕ := by
  classical
  exact Fintype.card {e : LectureEdges R // classCloneOf R a p hrow e = c ∧
    teacherCloneOf R b p hcol e = t}

noncomputable def pairCloneFiberGlobalEquiv {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (i : Fin m) (j : Fin n) (ci : Fin (a i)) (tj : Fin (b j)) :
    pairCloneFiber R a b p hrow hcol i j ci tj ≃
      {e : LectureEdges R // classCloneOf R a p hrow e = ⟨i, ci⟩ ∧
        teacherCloneOf R b p hcol e = ⟨j, tj⟩} where
  toFun z := by
    refine ⟨⟨i, ⟨j, z.1⟩⟩, ?_⟩
    constructor
    · change (⟨i, (classSlotEmbedding R a p hrow i ⟨j, z.1⟩).1⟩ : ClassClones a) = ⟨i, ci⟩
      have hci := congrArg Prod.fst z.2
      change (classSlotEmbedding R a p hrow i ⟨j, z.1⟩).1 = ci at hci
      exact Sigma.ext rfl (heq_of_eq hci)
    · change (⟨j, (teacherSlotEmbedding R b p hcol j ⟨i, z.1⟩).1⟩ : TeacherClones b) = ⟨j, tj⟩
      have htj := congrArg Prod.snd z.2
      change (teacherSlotEmbedding R b p hcol j ⟨i, z.1⟩).1 = tj at htj
      exact Sigma.ext rfl (heq_of_eq htj)
  invFun z := by
    rcases z with ⟨⟨i', ⟨j', k⟩⟩, hc, ht⟩
    have hi : i' = i := by
      have h := congrArg (fun c : ClassClones a => c.1) hc
      simpa [classCloneOf, globalClassSlotEmbedding] using h
    have hj : j' = j := by
      have h := congrArg (fun t : TeacherClones b => t.1) ht
      simpa [teacherCloneOf, globalTeacherSlotEmbedding] using h
    subst i'
    subst j'
    refine ⟨k, ?_⟩
    change ((classSlotEmbedding R a p hrow i ⟨j, k⟩).1,
      (teacherSlotEmbedding R b p hcol j ⟨i, k⟩).1) = (ci, tj)
    rcases Sigma.mk.inj_iff.mp hc with ⟨_, hci⟩
    rcases Sigma.mk.inj_iff.mp ht with ⟨_, htj⟩
    exact Prod.ext (eq_of_heq hci) (eq_of_heq htj)
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    rcases z with ⟨⟨i', ⟨j', k⟩⟩, hc, ht⟩
    have hi : i' = i := by
      have h := congrArg (fun c : ClassClones a => c.1) hc
      simpa [classCloneOf, globalClassSlotEmbedding] using h
    have hj : j' = j := by
      have h := congrArg (fun t : TeacherClones b => t.1) ht
      simpa [teacherCloneOf, globalTeacherSlotEmbedding] using h
    subst i'
    subst j'
    apply Subtype.ext
    rfl

theorem expandedRequirements_mass {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (i : Fin m) (j : Fin n) :
    (∑ ci : Fin (a i), ∑ tj : Fin (b j),
      expandedRequirements R a b p hrow hcol ⟨i, ci⟩ ⟨j, tj⟩) = R i j := by
  classical
  calc
    (∑ ci : Fin (a i), ∑ tj : Fin (b j),
        expandedRequirements R a b p hrow hcol ⟨i, ci⟩ ⟨j, tj⟩) =
        ∑ ci : Fin (a i), ∑ tj : Fin (b j),
          Fintype.card (pairCloneFiber R a b p hrow hcol i j ci tj) := by
            apply Finset.sum_congr rfl
            intro ci hci
            apply Finset.sum_congr rfl
            intro tj htj
            change Fintype.card {e : LectureEdges R //
              classCloneOf R a p hrow e = ⟨i, ci⟩ ∧
                teacherCloneOf R b p hcol e = ⟨j, tj⟩} = _
            exact (Fintype.card_congr
              (pairCloneFiberGlobalEquiv R a b p hrow hcol i j ci tj)).symm
    _ = R i j := pairCloneFiber_card_sum R a b p hrow hcol i j

noncomputable def classFiberPeriodEmbedding {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (p : ℕ) (hrow : ∀ i, rowSum R i ≤ p * a i)
    (c : ClassClones a) :
    {e : LectureEdges R // classCloneOf R a p hrow e = c} ↪ Fin p where
  toFun e := (classSlotEmbedding R a p hrow e.1.1 e.1.2).2
  inj' := by
    intro e₁ e₂ h
    apply Subtype.ext
    rcases e₁ with ⟨⟨i₁, edge₁⟩, hc₁⟩
    rcases e₂ with ⟨⟨i₂, edge₂⟩, hc₂⟩
    change (⟨i₁, (classSlotEmbedding R a p hrow i₁ edge₁).1⟩ : ClassClones a) = c at hc₁
    change (⟨i₂, (classSlotEmbedding R a p hrow i₂ edge₂).1⟩ : ClassClones a) = c at hc₂
    rcases Sigma.mk.inj_iff.mp (hc₁.trans hc₂.symm) with ⟨hi, hslot⟩
    subst i₂
    have hclone : (classSlotEmbedding R a p hrow i₁ edge₁).1 =
        (classSlotEmbedding R a p hrow i₁ edge₂).1 := eq_of_heq hslot
    have hperiod : (classSlotEmbedding R a p hrow i₁ edge₁).2 =
        (classSlotEmbedding R a p hrow i₁ edge₂).2 := h
    have hedge : classSlotEmbedding R a p hrow i₁ edge₁ =
        classSlotEmbedding R a p hrow i₁ edge₂ := Prod.ext hclone hperiod
    have := (classSlotEmbedding R a p hrow i₁).injective hedge
    cases this
    rfl

noncomputable def teacherFiberPeriodEmbedding {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (b : Fin n → ℕ) (p : ℕ) (hcol : ∀ j, colSum R j ≤ p * b j)
    (t : TeacherClones b) :
    {e : LectureEdges R // teacherCloneOf R b p hcol e = t} ↪ Fin p where
  toFun e := (teacherSlotEmbedding R b p hcol e.1.2.1 ⟨e.1.1, e.1.2.2⟩).2
  inj' := by
    intro e₁ e₂ h
    apply Subtype.ext
    rcases e₁ with ⟨⟨i₁, j₁, k₁⟩, ht₁⟩
    rcases e₂ with ⟨⟨i₂, j₂, k₂⟩, ht₂⟩
    change (⟨j₁, (teacherSlotEmbedding R b p hcol j₁ ⟨i₁, k₁⟩).1⟩ :
      TeacherClones b) = t at ht₁
    change (⟨j₂, (teacherSlotEmbedding R b p hcol j₂ ⟨i₂, k₂⟩).1⟩ :
      TeacherClones b) = t at ht₂
    rcases Sigma.mk.inj_iff.mp (ht₁.trans ht₂.symm) with ⟨hj, hslot⟩
    subst j₂
    have hclone : (teacherSlotEmbedding R b p hcol j₁ ⟨i₁, k₁⟩).1 =
        (teacherSlotEmbedding R b p hcol j₁ ⟨i₂, k₂⟩).1 := eq_of_heq hslot
    have hperiod : (teacherSlotEmbedding R b p hcol j₁ ⟨i₁, k₁⟩).2 =
        (teacherSlotEmbedding R b p hcol j₁ ⟨i₂, k₂⟩).2 := h
    have hedge : teacherSlotEmbedding R b p hcol j₁ ⟨i₁, k₁⟩ =
        teacherSlotEmbedding R b p hcol j₁ ⟨i₂, k₂⟩ := Prod.ext hclone hperiod
    have hedge' := (teacherSlotEmbedding R b p hcol j₁).injective hedge
    cases hedge'
    rfl

noncomputable def classFiberEquiv {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (c : ClassClones a) :
    {e : LectureEdges R // classCloneOf R a p hrow e = c} ≃
      Σ t : TeacherClones b,
        {e : LectureEdges R // classCloneOf R a p hrow e = c ∧
          teacherCloneOf R b p hcol e = t} where
  toFun e := ⟨teacherCloneOf R b p hcol e.1, ⟨e.1, e.2, rfl⟩⟩
  invFun e := ⟨e.2.1, e.2.2.1⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    rcases e with ⟨t, ⟨edge, hc, ht⟩⟩
    cases ht
    rfl

noncomputable def teacherFiberEquiv {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (t : TeacherClones b) :
    {e : LectureEdges R // teacherCloneOf R b p hcol e = t} ≃
      Σ c : ClassClones a,
        {e : LectureEdges R // classCloneOf R a p hrow e = c ∧
          teacherCloneOf R b p hcol e = t} where
  toFun e := ⟨classCloneOf R a p hrow e.1, ⟨e.1, rfl, e.2⟩⟩
  invFun e := ⟨e.2.1, e.2.2.2⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    rcases e with ⟨c, ⟨edge, hc, ht⟩⟩
    cases hc
    rfl

theorem rowSum_expandedRequirements_le {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (c : ClassClones a) :
    (∑ t : TeacherClones b, expandedRequirements R a b p hrow hcol c t) ≤ p := by
  classical
  have hcard : (∑ t : TeacherClones b,
      expandedRequirements R a b p hrow hcol c t) =
      Fintype.card {e : LectureEdges R // classCloneOf R a p hrow e = c} := by
    calc
      (∑ t : TeacherClones b, expandedRequirements R a b p hrow hcol c t) =
          ∑ t : TeacherClones b, Fintype.card {e : LectureEdges R //
            classCloneOf R a p hrow e = c ∧ teacherCloneOf R b p hcol e = t} := rfl
      _ = Fintype.card (Σ t : TeacherClones b, {e : LectureEdges R //
            classCloneOf R a p hrow e = c ∧ teacherCloneOf R b p hcol e = t}) :=
          (Fintype.card_sigma).symm
      _ = Fintype.card {e : LectureEdges R // classCloneOf R a p hrow e = c} :=
          (Fintype.card_congr (classFiberEquiv R a b p hrow hcol c)).symm
  rw [hcard]
  simpa using Fintype.card_le_of_injective
    (classFiberPeriodEmbedding R a p hrow c) (classFiberPeriodEmbedding R a p hrow c).injective

theorem colSum_expandedRequirements_le {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (t : TeacherClones b) :
    (∑ c' : ClassClones a, expandedRequirements R a b p hrow hcol c' t) ≤ p := by
  classical
  have hcard : (∑ c' : ClassClones a,
      expandedRequirements R a b p hrow hcol c' t) =
      Fintype.card {e : LectureEdges R // teacherCloneOf R b p hcol e = t} := by
    calc
      (∑ c' : ClassClones a, expandedRequirements R a b p hrow hcol c' t) =
          ∑ c : ClassClones a, Fintype.card {e : LectureEdges R //
            classCloneOf R a p hrow e = c ∧ teacherCloneOf R b p hcol e = t} := rfl
      _ = Fintype.card (Σ c : ClassClones a, {e : LectureEdges R //
            classCloneOf R a p hrow e = c ∧ teacherCloneOf R b p hcol e = t}) :=
          (Fintype.card_sigma).symm
      _ = Fintype.card {e : LectureEdges R // teacherCloneOf R b p hcol e = t} :=
          (Fintype.card_congr (teacherFiberEquiv R a b p hrow hcol t)).symm
  rw [hcard]
  simpa using Fintype.card_le_of_injective
    (teacherFiberPeriodEmbedding R b p hcol t) (teacherFiberPeriodEmbedding R b p hcol t).injective

noncomputable def aggregateSchedule {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (p : ℕ) (y : ClassClones a → TeacherClones b → Fin p → ℕ) :
    Fin m → Fin n → Fin p → ℕ := fun i j k =>
      ∑ ci : Fin (a i), ∑ tj : Fin (b j), y ⟨i, ci⟩ ⟨j, tj⟩ k

def IsCT1On {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → ℕ) (p : ℕ) (y : α → β → Fin p → ℕ) : Prop :=
  (∀ a b, ∑ k, y a b k = R a b) ∧
  (∀ a k, ∑ b, y a b k ≤ 1) ∧
  (∀ b k, ∑ a, y a b k ≤ 1) ∧
  (∀ a b k, y a b k ≤ 1)

theorem ct1On_of_bounds {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → ℕ) (p : ℕ)
    (hcol : ∀ b, (∑ a, R a b) ≤ p) (hrow : ∀ a, (∑ b, R a b) ≤ p) :
    ∃ y : α → β → Fin p → ℕ, IsCT1On R p y := by
  classical
  let ea := Fintype.equivFin α
  let eb := Fintype.equivFin β
  let Rfin : Fin (Fintype.card α) → Fin (Fintype.card β) → ℕ :=
    fun i j => R (ea.symm i) (eb.symm j)
  have hcolFin : ∀ j, colSum Rfin j ≤ p := by
    intro j
    change (∑ i : Fin (Fintype.card α), R (ea.symm i) (eb.symm j)) ≤ p
    have hs : (∑ i : Fin (Fintype.card α), R (ea.symm i) (eb.symm j)) =
        ∑ a : α, R a (eb.symm j) := by
      exact Fintype.sum_equiv ea.symm _ _ (by intro i; rfl)
    rw [hs]
    exact hcol (eb.symm j)
  have hrowFin : ∀ i, rowSum Rfin i ≤ p := by
    intro i
    change (∑ j : Fin (Fintype.card β), R (ea.symm i) (eb.symm j)) ≤ p
    have hs : (∑ j : Fin (Fintype.card β), R (ea.symm i) (eb.symm j)) =
        ∑ b : β, R (ea.symm i) b := by
      exact Fintype.sum_equiv eb.symm _ _ (by intro j; rfl)
    rw [hs]
    exact hrow (ea.symm i)
  obtain ⟨z, hz⟩ := (Timetabling85.ClassTeacher.prop_2_1 Rfin p).2 ⟨hcolFin, hrowFin⟩
  refine ⟨fun a b k => z (ea a) (eb b) k, ?_⟩
  constructor
  · intro a b
    simpa [Rfin] using hz.1 (ea a) (eb b)
  constructor
  · intro a k
    have hs : (∑ b : β, z (ea a) (eb b) k) =
        ∑ j : Fin (Fintype.card β), z (ea a) j k := by
      exact Fintype.sum_equiv eb _ _ (by intro b; rfl)
    rw [hs]
    exact hz.2.1 (ea a) k
  constructor
  · intro b k
    have hs : (∑ a : α, z (ea a) (eb b) k) =
        ∑ i : Fin (Fintype.card α), z i (eb b) k := by
      exact Fintype.sum_equiv ea _ _ (by intro a; rfl)
    rw [hs]
    exact hz.2.2.1 (eb b) k
  · intro a b k
    exact hz.2.2.2 (ea a) (eb b) k

theorem aggregate_expanded_schedule {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ) (p : ℕ)
    (hrow : ∀ i, rowSum R i ≤ p * a i) (hcol : ∀ j, colSum R j ≤ p * b j)
    (hmass : ∀ i j, ∑ ci : Fin (a i), ∑ tj : Fin (b j),
      expandedRequirements R a b p hrow hcol ⟨i, ci⟩ ⟨j, tj⟩ = R i j)
    (y : ClassClones a → TeacherClones b → Fin p → ℕ)
    (hy : IsCT1On (expandedRequirements R a b p hrow hcol) p y) :
    IsCT2 R p a b (aggregateSchedule a b p y) := by
  classical
  rcases hy with ⟨hsched, hclass, hteacher, h01⟩
  constructor
  · intro i j
    change (∑ k, aggregateSchedule a b p y i j k) = R i j
    calc
      ∑ k, aggregateSchedule a b p y i j k =
          ∑ ci : Fin (a i), ∑ tj : Fin (b j),
            ∑ k, y ⟨i, ci⟩ ⟨j, tj⟩ k := by
              unfold aggregateSchedule
              calc
                (∑ k : Fin p, ∑ ci : Fin (a i), ∑ tj : Fin (b j),
                  y ⟨i, ci⟩ ⟨j, tj⟩ k) =
                    ∑ ci : Fin (a i), ∑ k : Fin p, ∑ tj : Fin (b j),
                      y ⟨i, ci⟩ ⟨j, tj⟩ k := by
                        exact Finset.sum_comm
                _ = ∑ ci : Fin (a i), ∑ tj : Fin (b j), ∑ k : Fin p,
                      y ⟨i, ci⟩ ⟨j, tj⟩ k := by
                        apply Finset.sum_congr rfl
                        intro ci hci
                        exact Finset.sum_comm
      _ = R i j := by
        calc
          (∑ ci : Fin (a i), ∑ tj : Fin (b j),
              ∑ k, y ⟨i, ci⟩ ⟨j, tj⟩ k) =
              ∑ ci : Fin (a i), ∑ tj : Fin (b j),
                expandedRequirements R a b p hrow hcol ⟨i, ci⟩ ⟨j, tj⟩ := by
                  apply Finset.sum_congr rfl
                  intro ci hci
                  apply Finset.sum_congr rfl
                  intro tj htj
                  exact hsched ⟨i, ci⟩ ⟨j, tj⟩
          _ = R i j := hmass i j
  · constructor
    · intro i k
      change (∑ j, aggregateSchedule a b p y i j k) ≤ a i
      calc
        ∑ j, aggregateSchedule a b p y i j k =
            ∑ ci : Fin (a i), ∑ j, ∑ tj : Fin (b j), y ⟨i, ci⟩ ⟨j, tj⟩ k := by
              unfold aggregateSchedule
              exact Finset.sum_comm
        _ = ∑ ci : Fin (a i), ∑ t : TeacherClones b,
              y ⟨i, ci⟩ t k := by
                congr 1
                funext ci
                exact (Fintype.sum_sigma (fun t : TeacherClones b =>
                  y ⟨i, ci⟩ t k)).symm
        _ ≤ ∑ _ci : Fin (a i), 1 :=
              Finset.sum_le_sum fun ci _ => hclass ⟨i, ci⟩ k
        _ = a i := by simp
    · intro j k
      change (∑ i, aggregateSchedule a b p y i j k) ≤ b j
      calc
        ∑ i, aggregateSchedule a b p y i j k =
            ∑ tj : Fin (b j), ∑ i, ∑ ci : Fin (a i), y ⟨i, ci⟩ ⟨j, tj⟩ k := by
              unfold aggregateSchedule
              calc
                (∑ i : Fin m, ∑ ci : Fin (a i), ∑ tj : Fin (b j),
                    y ⟨i, ci⟩ ⟨j, tj⟩ k) =
                    ∑ c : ClassClones a, ∑ tj : Fin (b j), y c ⟨j, tj⟩ k := by
                      exact (Fintype.sum_sigma (fun c : ClassClones a =>
                        ∑ tj : Fin (b j), y c ⟨j, tj⟩ k)).symm
                _ = ∑ tj : Fin (b j), ∑ c : ClassClones a, y c ⟨j, tj⟩ k :=
                      Finset.sum_comm
                _ = ∑ tj : Fin (b j), ∑ i : Fin m, ∑ ci : Fin (a i),
                      y ⟨i, ci⟩ ⟨j, tj⟩ k := by
                      apply Finset.sum_congr rfl
                      intro tj htj
                      exact Fintype.sum_sigma (fun c : ClassClones a => y c ⟨j, tj⟩ k)
        _ = ∑ tj : Fin (b j), ∑ c : ClassClones a,
              y c ⟨j, tj⟩ k := by
                congr 1
                funext tj
                exact (Fintype.sum_sigma (fun c : ClassClones a =>
                  y c ⟨j, tj⟩ k)).symm
        _ ≤ ∑ _tj : Fin (b j), 1 :=
              Finset.sum_le_sum fun tj _ => hteacher ⟨j, tj⟩ k
        _ = b j := by simp

theorem ct2_suff_of_bounds {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ)
    (hcol : ∀ j, colSum R j ≤ p * b j) (hrow : ∀ i, rowSum R i ≤ p * a i) :
    ∃ x : Fin m → Fin n → Fin p → ℕ, IsCT2 R p a b x := by
  classical
  let E := expandedRequirements R a b p hrow hcol
  have hmass : ∀ i j, ∑ ci : Fin (a i), ∑ tj : Fin (b j),
      E ⟨i, ci⟩ ⟨j, tj⟩ = R i j := by
    intro i j
    exact expandedRequirements_mass R a b p hrow hcol i j
  obtain ⟨y, hy⟩ := ct1On_of_bounds E p
    (fun t => colSum_expandedRequirements_le R a b p hrow hcol t)
    (fun c => rowSum_expandedRequirements_le R a b p hrow hcol c)
  exact ⟨aggregateSchedule a b p y, aggregate_expanded_schedule R a b p hrow hcol
    hmass y hy⟩

end Timetabling85.ClassTeacher

#print axioms Timetabling85.ClassTeacher.classSlotEmbedding
#print axioms Timetabling85.ClassTeacher.teacherSlotEmbedding

theorem solution {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    (∃ x : Fin m → Fin n → Fin p → ℕ,
      Timetabling85.ClassTeacher.IsCT2 R p a b x) ↔
      (∀ j, Timetabling85.ClassTeacher.colSum R j ≤ p * b j) ∧
        (∀ i, Timetabling85.ClassTeacher.rowSum R i ≤ p * a i) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases hx with ⟨hsched, hclass, hteacher⟩
    constructor
    · intro j
      calc
        Timetabling85.ClassTeacher.colSum R j = ∑ i, ∑ k, x i j k := by
          simp only [Timetabling85.ClassTeacher.colSum]
          apply Finset.sum_congr rfl
          intro i hi
          exact (hsched i j).symm
        _ = ∑ k, ∑ i, x i j k := Finset.sum_comm
        _ ≤ ∑ k, b j := Finset.sum_le_sum fun k hk => hteacher j k
        _ = p * b j := by simp
    · intro i
      calc
        Timetabling85.ClassTeacher.rowSum R i = ∑ j, ∑ k, x i j k := by
          simp only [Timetabling85.ClassTeacher.rowSum]
          apply Finset.sum_congr rfl
          intro j hj
          exact (hsched i j).symm
        _ = ∑ k, ∑ j, x i j k := Finset.sum_comm
        _ ≤ ∑ k, a i := Finset.sum_le_sum fun k hk => hclass i k
        _ = p * a i := by simp
  · rintro ⟨hcol, hrow⟩
    exact Timetabling85.ClassTeacher.ct2_suff_of_bounds R p a b hcol hrow

#print axioms solution
