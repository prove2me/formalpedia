-- Prove2me | solution 1 for TwinWidthI.BallGraph.redPath_le_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:31:49.647124+00:00
-- url     : https://prove2.me/submissions/5a60b854-abac-4c19-ab4f-39be94de2347

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting
open TwinWidthI.BallGraph
open Finset

theorem tw_merge_exists {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (univ : Finset V)) {X Y : Finset V} (hX : X ∈ P.parts) (hY : Y ∈ P.parts)
    (hXY : X ≠ Y) :
    ∃ Q : Finpartition (univ : Finset V),
      Q.parts = insert (X ∪ Y) ((P.parts.erase X).erase Y) := by
  classical
  set S : Finset (Finset V) := insert (X ∪ Y) ((P.parts.erase X).erase Y) with hS
  have hXne : X ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (P.nonempty_of_mem_parts hX)
  have hbot : (∅ : Finset V) ∉ S := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hXne (Finset.union_eq_empty.mp h.symm).1
    · have := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
      exact P.bot_notMem this
  have hdisj : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → Disjoint A B :=
    fun A hA B hB hAB => P.disjoint hA hB hAB
  have hind : S.SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hAB
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hS] at hA hB
    simp only [Function.onFun, id]
    have memP : ∀ {Z}, Z ∈ (P.parts.erase X).erase Y → Z ∈ P.parts ∧ Z ≠ X ∧ Z ≠ Y := by
      intro Z hZ
      exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hZ),
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hZ), Finset.ne_of_mem_erase hZ⟩
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact absurd rfl hAB
    · obtain ⟨hB1, hB2, hB3⟩ := memP hB
      exact Finset.disjoint_union_left.mpr
        ⟨hdisj _ hX _ hB1 (Ne.symm hB2), hdisj _ hY _ hB1 (Ne.symm hB3)⟩
    · obtain ⟨hA1, hA2, hA3⟩ := memP hA
      exact Finset.disjoint_union_right.mpr
        ⟨hdisj _ hA1 _ hX hA2, hdisj _ hA1 _ hY hA3⟩
    · exact hdisj _ (memP hA).1 _ (memP hB).1 hAB
  have hsup : S.sup id = univ := by
    apply Finset.eq_univ_of_forall
    intro v
    have hv : v ∈ (univ : Finset V) := Finset.mem_univ v
    rw [← P.sup_parts] at hv
    obtain ⟨Z, hZ, hvZ⟩ := Finset.mem_sup.mp hv
    rw [Finset.mem_sup]
    by_cases h1 : Z = X
    · exact ⟨X ∪ Y, Finset.mem_insert_self _ _, Finset.mem_union_left _ (h1 ▸ hvZ)⟩
    by_cases h2 : Z = Y
    · exact ⟨X ∪ Y, Finset.mem_insert_self _ _, Finset.mem_union_right _ (h2 ▸ hvZ)⟩
    exact ⟨Z, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hZ⟩⟩),
      hvZ⟩
  refine ⟨Finpartition.ofErase S hind hsup, ?_⟩
  simp only [Finpartition.ofErase]
  exact Finset.erase_eq_of_notMem hbot


/-- A vertex set of `Fin n` is an interval. -/
def RpInterval {n : ℕ} (X : Finset (Fin n)) : Prop :=
  ∀ a ∈ X, ∀ c ∈ X, ∀ v : Fin n, a ≤ v → v ≤ c → v ∈ X

theorem rp_eq_of_common {n : ℕ} (P : Finpartition (univ : Finset (Fin n)))
    {Y₁ Y₂ : Finset (Fin n)} (h₁ : Y₁ ∈ P.parts) (h₂ : Y₂ ∈ P.parts) {y : Fin n}
    (hy₁ : y ∈ Y₁) (hy₂ : y ∈ Y₂) : Y₁ = Y₂ := by
  by_contra hne
  exact Finset.disjoint_left.mp (P.disjoint h₁ h₂ hne) hy₁ hy₂

theorem rp_exists_part {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) (v : Fin n) :
    ∃ Z ∈ P.parts, v ∈ Z := by
  obtain ⟨Z, hZ, hvZ⟩ := P.exists_mem (Finset.mem_univ v)
  exact ⟨Z, hZ, hvZ⟩

theorem rp_deg {n : ℕ} (P : Finpartition (univ : Finset (Fin n)))
    (hI : ∀ X ∈ P.parts, RpInterval X) : IsRedDPartition (SimpleGraph.pathGraph n) P 2 := by
  classical
  intro X hX
  have hne := P.nonempty_of_mem_parts hX
  set hi := X.max' hne with hhi
  set lo := X.min' hne with hlo
  set A := P.parts.filter (fun Y => ∃ y ∈ Y, y.val = hi.val + 1) with hA
  set B := P.parts.filter (fun Y => ∃ y ∈ Y, y.val + 1 = lo.val) with hB
  have hA1 : #A ≤ 1 := by
    refine Finset.card_le_one.mpr fun Y₁ h₁ Y₂ h₂ => ?_
    obtain ⟨h₁P, y₁, hy₁, e₁⟩ := Finset.mem_filter.mp h₁
    obtain ⟨h₂P, y₂, hy₂, e₂⟩ := Finset.mem_filter.mp h₂
    have : y₁ = y₂ := Fin.ext (by omega)
    subst this
    exact rp_eq_of_common P h₁P h₂P hy₁ hy₂
  have hB1 : #B ≤ 1 := by
    refine Finset.card_le_one.mpr fun Y₁ h₁ Y₂ h₂ => ?_
    obtain ⟨h₁P, y₁, hy₁, e₁⟩ := Finset.mem_filter.mp h₁
    obtain ⟨h₂P, y₂, hy₂, e₂⟩ := Finset.mem_filter.mp h₂
    have : y₁ = y₂ := Fin.ext (by omega)
    subst this
    exact rp_eq_of_common P h₁P h₂P hy₁ hy₂
  have hsub : P.parts.filter (fun Y => Y ≠ X ∧ SomeEdge (SimpleGraph.pathGraph n) X Y) ⊆ A ∪ B := by
    intro Y hY
    obtain ⟨hYP, hYX, x, hx, y, hy, hadj⟩ := Finset.mem_filter.mp hY
    have hyX : y ∉ X := fun h => hYX (rp_eq_of_common P hYP hX hy h)
    have hxhi : x ≤ hi := X.le_max' x hx
    have hlox : lo ≤ x := X.min'_le x hx
    rcases SimpleGraph.pathGraph_adj.mp hadj with h | h
    · apply Finset.mem_union_left
      refine Finset.mem_filter.mpr ⟨hYP, y, hy, ?_⟩
      have hlt : hi < y := by
        by_contra hle
        push_neg at hle
        exact hyX (hI X hX x hx hi (X.max'_mem hne) y (Fin.le_def.mpr (by omega)) hle)
      rw [Fin.le_def] at hxhi
      rw [Fin.lt_def] at hlt
      omega
    · apply Finset.mem_union_right
      refine Finset.mem_filter.mpr ⟨hYP, y, hy, ?_⟩
      have hlt : y < lo := by
        by_contra hle
        push_neg at hle
        exact hyX (hI X hX lo (X.min'_mem hne) x hx y hle (Fin.le_def.mpr (by omega)))
      rw [Fin.le_def] at hlox
      rw [Fin.lt_def] at hlt
      omega
  calc #(P.parts.filter (fun Y => Y ≠ X ∧ SomeEdge (SimpleGraph.pathGraph n) X Y))
      ≤ #(A ∪ B) := Finset.card_le_card hsub
    _ ≤ #A + #B := Finset.card_union_le _ _
    _ ≤ 2 := by omega

theorem rp_chain {n : ℕ} :
    ∀ (k : ℕ) (P : Finpartition (univ : Finset (Fin n))), #P.parts = k →
      (∀ X ∈ P.parts, RpInterval X) →
      ∃ (M : ℕ) (Ps : Fin (M + 1) → Finpartition (univ : Finset (Fin n))),
        Ps 0 = P ∧ #(Ps (Fin.last M)).parts ≤ 1 ∧
        (∀ i : Fin M, TwinWidthI.BoolWidth.IsMergeStep (Ps i.castSucc) (Ps i.succ)) ∧
        ∀ i, ∀ X ∈ (Ps i).parts, RpInterval X := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P hk hI
    by_cases hle : #P.parts ≤ 1
    · exact ⟨0, fun _ => P, rfl, hle, fun i => Fin.elim0 i, fun _ => hI⟩
    · push_neg at hle
      obtain ⟨X₁, hX₁, X₂, hX₂, hX12⟩ := Finset.one_lt_card.mp hle
      obtain ⟨w₀, -⟩ := P.nonempty_of_mem_parts hX₁
      have hn : 0 < n := Fin.pos w₀
      set z₀ : Fin n := ⟨0, hn⟩
      obtain ⟨X, hX, hz₀⟩ := rp_exists_part P z₀
      have hout : ∃ m : ℕ, ∃ v : Fin n, v.val = m ∧ v ∉ X := by
        have : ∃ Z ∈ P.parts, Z ≠ X := by
          by_cases h : X₁ = X
          · exact ⟨X₂, hX₂, fun h' => hX12 (h.trans h'.symm)⟩
          · exact ⟨X₁, hX₁, h⟩
        obtain ⟨Z, hZ, hZX⟩ := this
        obtain ⟨w, hw⟩ := P.nonempty_of_mem_parts hZ
        exact ⟨w.val, w, rfl, fun h => hZX (rp_eq_of_common P hZ hX hw h)⟩
      classical
      set m₀ := Nat.find hout with hm₀
      obtain ⟨v, hvval, hvX⟩ := Nat.find_spec hout
      have hbelow : ∀ t : Fin n, t.val < v.val → t ∈ X := by
        intro t ht
        by_contra htX
        have := Nat.find_min' hout ⟨t, rfl, htX⟩
        omega
      have habove : ∀ x ∈ X, x.val < v.val := by
        intro x hx
        by_contra hge
        push_neg at hge
        exact hvX (hI X hX z₀ hz₀ x hx v (Fin.le_def.mpr (Nat.zero_le _))
          (Fin.le_def.mpr hge))
      obtain ⟨Y, hY, hvY⟩ := rp_exists_part P v
      have hXY : X ≠ Y := fun h => hvX (h ▸ hvY)
      have hUI : RpInterval (X ∪ Y) := by
        intro a ha c hc t hat htc
        by_cases htv : t.val < v.val
        · exact Finset.mem_union_left _ (hbelow t htv)
        · push_neg at htv
          have hcX : c ∉ X := fun h => by
            have := habove c h
            rw [Fin.le_def] at htc
            omega
          have hcY : c ∈ Y := (Finset.mem_union.mp hc).resolve_left hcX
          exact Finset.mem_union_right _ (hI Y hY v hvY c hcY t (Fin.le_def.mpr htv) htc)
      obtain ⟨Q, hQ⟩ := tw_merge_exists P hX hY hXY
      have hQI : ∀ Z ∈ Q.parts, RpInterval Z := by
        intro Z hZ
        rw [hQ] at hZ
        rcases Finset.mem_insert.mp hZ with rfl | hZ
        · exact hUI
        · exact hI Z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hZ))
      have hcard : #Q.parts < k := by
        rw [hQ, ← hk]
        have h1 := Finset.card_insert_le (X ∪ Y) ((P.parts.erase X).erase Y)
        have h2 : #((P.parts.erase X).erase Y) = #P.parts - 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hXY, hY⟩),
            Finset.card_erase_of_mem hX]
          omega
        omega
      obtain ⟨M, Ps, h0, hlast, hstep, hPsI⟩ := ih _ hcard Q rfl hQI
      refine ⟨M + 1, Fin.cons P Ps, rfl, ?_, ?_, ?_⟩
      · rw [← Fin.succ_last, Fin.cons_succ]; exact hlast
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one]
          rw [show (1 : Fin (M + 2)) = (0 : Fin (M + 1)).succ from rfl, Fin.cons_succ, h0]
          exact ⟨X, hX, Y, hY, hXY, hQ⟩
        · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact hstep j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hI
        · rw [Fin.cons_succ]; exact hPsI j

theorem solution (n : ℕ) : RedTwinWidthLE (SimpleGraph.pathGraph n) 2 := by
  have hbot : ∀ X ∈ (⊥ : Finpartition (univ : Finset (Fin n))).parts, RpInterval X := by
    intro X hX
    obtain ⟨a, -, rfl⟩ := Finpartition.mem_bot_iff.mp hX
    intro b hb c hc v hbv hvc
    rw [Finset.mem_singleton] at hb hc ⊢
    subst hb; subst hc
    exact le_antisymm hvc hbv
  obtain ⟨M, Ps, h0, hl, hs, hI⟩ := rp_chain _ (⊥ : Finpartition (univ : Finset (Fin n))) rfl hbot
  exact ⟨M, Ps, h0, hl, hs, fun i => rp_deg _ (hI i)⟩
