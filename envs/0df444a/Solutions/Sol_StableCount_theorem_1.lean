-- Prove2me | solution 1 for StableCount.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:44:00.266827+00:00
-- url     : https://prove2.me/submissions/e282e49f-b3c0-4a0a-902a-c6b3b57c97ac

import Mathlib
import Theorems.Thm_StableCount_lemma_3_1
import Theorems.Thm_StableCount_proposition_2_3
import Definitions.Def_StableCount_Member
import Theorems.Thm_StableCount_lemma_3_2
import Theorems.Thm_StableCount_theorem_2
import Theorems.Thm_StableCount_theorem_3
import Theorems.Thm_StableCount_proposition_2_5

section
namespace StableCount

open StableMatching

namespace Dev.Chain

variable {n : ℕ}

/-- the instance with the two sides exchanged -/
def swapInst (I : Instance n) : Instance n := ⟨I.womanRank, I.manRank⟩

theorem swap_stable (I : Instance n) (ν : Matching n) :
    (swapInst I).IsStable ν ↔ I.IsStable ν.symm := by
  unfold Instance.IsStable Instance.IsBlockingPair Instance.manPrefers Instance.womanPrefers
  constructor
  · intro h m w ⟨h1, h2⟩
    exact h w m ⟨h2, h1⟩
  · intro h m w ⟨h1, h2⟩
    exact h w m ⟨h2, h1⟩

theorem swap_manOptimal (I : Instance n) (ν : Matching n) :
    IsManOptimal (swapInst I) ν ↔ IsWomanOptimal I ν.symm := by
  unfold IsManOptimal IsWomanOptimal
  rw [swap_stable]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun ν' hν' w => ?_⟩
    have := h ν'.symm ((swap_stable I _).mpr (by simpa using hν')) w
    simpa [swapInst] using this
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun ν' hν' w => ?_⟩
    have := h ν'.symm ((swap_stable I _).mp hν') w
    simpa [swapInst] using this

theorem exists_womanOptimal (I : Instance n) : ∃ μ, IsWomanOptimal I μ := by
  obtain ⟨μM, hM, -⟩ := lemma_3_1 (swapInst I)
  exact ⟨μM.symm, (swap_manOptimal I μM).mp hM⟩

/-- the sum of the ranks of the men's partners -/
def phi (I : Instance n) (μ : Matching n) : ℕ := ∑ m : Fin n, ((I.manRank m (μ m) : Fin n) : ℕ)

theorem phi_lt (I : Instance n) {a b : Matching n} (h : MatchingLT I a b) : phi I a < phi I b := by
  obtain ⟨hle, hne⟩ := h
  unfold phi
  apply Finset.sum_lt_sum
  · intro m _; exact hle m
  · by_contra hcon
    push_neg at hcon
    apply hne
    ext m
    have h1 := hle m
    have h2 := hcon m (Finset.mem_univ _)
    have : I.manRank m (a m) = I.manRank m (b m) := le_antisymm h1 h2
    exact congrArg Fin.val ((I.manRank m).injective this)

theorem LE_trans (I : Instance n) {a b c : Matching n} (h1 : MatchingLE I a b)
    (h2 : MatchingLE I b c) : MatchingLE I a c := fun m => (h1 m).trans (h2 m)

open Classical in
theorem chain_aux (I : Instance n) : ∀ (k : ℕ) (a b : Matching n), I.IsStable a → I.IsStable b →
    MatchingLE I a b → phi I b - phi I a = k →
    ∃ (R : ℕ) (μ : Fin (R + 1) → Matching n), μ 0 = a ∧ μ (Fin.last R) = b ∧
      ∀ i : Fin R, Covers I (μ i.castSucc) (μ i.succ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a b ha hb hab hk
    by_cases heq : a = b
    · subst heq
      exact ⟨0, fun _ => a, rfl, rfl, fun i => i.elim0⟩
    · have hlt : MatchingLT I a b := ⟨hab, heq⟩
      set T : Finset (Matching n) := Finset.univ.filter fun η =>
        I.IsStable η ∧ MatchingLT I a η ∧ MatchingLE I η b with hT
      have hTne : T.Nonempty := ⟨b, by
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hb, hlt, fun m => le_rfl⟩⟩
      obtain ⟨η, hηT, hmin⟩ := Finset.exists_min_image T (phi I) hTne
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hηT
      obtain ⟨hη, haη, hηb⟩ := hηT
      have hcov : Covers I a η := by
        refine ⟨ha, hη, haη, fun ζ hζ ⟨h1, h2⟩ => ?_⟩
        have hζT : ζ ∈ T := by
          simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hζ, h1, LE_trans I h2.1 hηb⟩
        have := hmin ζ hζT
        have := phi_lt I h2
        omega
      have p1 := phi_lt I haη
      have p2 : phi I η ≤ phi I b := by
        rcases (show MatchingLE I η b from hηb) with _
        by_cases hb' : η = b
        · rw [hb']
        · exact (phi_lt I ⟨hηb, hb'⟩).le
      obtain ⟨R, μ, h0, hl, hc⟩ := ih (phi I b - phi I η) (by omega) η b hη hb hηb rfl
      refine ⟨R + 1, Fin.cons a μ, rfl, ?_, ?_⟩
      · simpa [Fin.cons_succ, ← Fin.succ_last] using hl
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [h0] using hcov
        · simpa using hc j

theorem exists_chain (I : Instance n) : ∃ (R : ℕ) (μ : Fin (R + 1) → Matching n), IsMaximalChain I μ := by
  obtain ⟨μM, hM, -⟩ := lemma_3_1 I
  obtain ⟨μW, hW⟩ := exists_womanOptimal I
  have hle : MatchingLE I μM μW := fun m => hM.2 μW hW.1 m
  obtain ⟨R, μ, h0, hl, hc⟩ := chain_aux I _ μM μW hM.1 hW.1 hle rfl
  refine ⟨R, μ, ?_, ?_, hc⟩
  · rw [h0]; exact hM
  · rw [hl]; exact hW

end Dev.Chain

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.Deg

variable {n : ℕ}

theorem card_P {α : Type*} [DecidableEq α] (P : Finset α) (R : ℕ) (p : Fin (R + 1) → α)
    (rk : α → ℤ) (hinj : Function.Injective rk) (h1 : ∀ m, p m ∈ P)
    (h2 : ∀ i : Fin R, p i.castSucc = p i.succ ∨ rk (p i.castSucc) < rk (p i.succ))
    (h3 : ∀ i : Fin R, p i.castSucc ≠ p i.succ → ∀ w ∈ P,
      ¬ (rk (p i.castSucc) < rk w ∧ rk w < rk (p i.succ)))
    (h4 : ∀ w ∈ P, rk (p 0) ≤ rk w ∧ rk w ≤ rk (p (Fin.last R))) :
    P.card = (Finset.univ.filter fun i : Fin R => p i.castSucc ≠ p i.succ).card + 1 := by
  classical
  -- monotonicity along the chain
  have hmono : ∀ a b : Fin (R + 1), a ≤ b → rk (p a) ≤ rk (p b) := by
    intro a b hab
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have hab' : a ≤ b := hab
    induction b, hab' using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab' ih =>
      have hbR : b < R := by omega
      have := ih (by omega) (Fin.mk_le_mk.mpr hab')
      have h2' := h2 ⟨b, hbR⟩
      have e1 : (⟨b, hbR⟩ : Fin R).castSucc = ⟨b, by omega⟩ := rfl
      have e2 : (⟨b, hbR⟩ : Fin R).succ = ⟨b + 1, hb⟩ := rfl
      rw [e1, e2] at h2'
      rcases h2' with h | h
      · rw [← h]; exact this
      · exact this.trans h.le
  have himg : P = Finset.univ.image p := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hw
      obtain ⟨hlo, hhi⟩ := h4 w hw
      -- the last index whose rank is at most `rk w`
      set T : Finset (Fin (R + 1)) := Finset.univ.filter fun m => rk (p m) ≤ rk w with hT
      have hTne : T.Nonempty := ⟨0, by simp [hT, hlo]⟩
      set m := T.max' hTne with hm
      have hmT : rk (p m) ≤ rk w := by
        have := T.max'_mem hTne
        simpa [hT] using this
      by_cases heq : rk (p m) = rk w
      · exact ⟨m, hinj heq⟩
      · exfalso
        have hlt : rk (p m) < rk w := lt_of_le_of_ne hmT heq
        have hmlast : m ≠ Fin.last R := by
          intro hml
          rw [hml] at hlt
          linarith
        obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr hmlast
        have hnext : rk w < rk (p j.succ) := by
          by_contra hcon
          push_neg at hcon
          have hmem : j.succ ∈ T := by simp [hT, hcon]
          have := T.le_max' _ hmem
          rw [← hm, ← hj] at this
          exact absurd this (by
            rw [Fin.le_def]; simp [Fin.val_succ, Fin.val_castSucc])
        have hne : p j.castSucc ≠ p j.succ := by
          intro hh
          rw [← hj, hh] at hlt
          linarith
        exact h3 j hne w hw ⟨by rw [hj]; exact hlt, hnext⟩
    · rintro ⟨m, rfl⟩
      exact h1 m
  rw [himg]
  set M : Finset (Fin R) := Finset.univ.filter fun i => p i.castSucc ≠ p i.succ with hM
  have hstrict : ∀ i ∈ M, rk (p i.castSucc) < rk (p i.succ) := by
    intro i hi
    simp only [hM, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases h2 i with h | h
    · exact absurd h hi
    · exact h
  have hdecomp : Finset.univ.image p = insert (p 0) (M.image fun i => p i.succ) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨m, hm⟩ := m
      induction m with
      | zero => left; rfl
      | succ m ih =>
        have hmR : m < R := by omega
        by_cases hmv : p ⟨m, by omega⟩ = p ⟨m + 1, hm⟩
        · rw [← hmv]; exact ih (by omega)
        · right
          refine ⟨⟨m, hmR⟩, ?_, rfl⟩
          simp only [hM, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmv
    · rintro (rfl | ⟨i, -, rfl⟩)
      · exact ⟨0, rfl⟩
      · exact ⟨i.succ, rfl⟩
  rw [hdecomp, Finset.card_insert_of_notMem, Finset.card_image_of_injOn]
  · intro i hi j hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1' : rk (p i.succ) ≤ rk (p j.castSucc) := hmono _ _ (by
        rw [Fin.le_def]; simp [Fin.val_succ, Fin.val_castSucc]; exact hlt)
      have := hstrict j hj
      have h5 := hinj (congrArg rk hij) 
      have := congrArg rk hij
      simp only at this
      linarith
    · have h1' : rk (p j.succ) ≤ rk (p i.castSucc) := hmono _ _ (by
        rw [Fin.le_def]; simp [Fin.val_succ, Fin.val_castSucc]; exact hlt)
      have := hstrict i hi
      have := congrArg rk hij
      simp only at this
      linarith
  · simp only [Finset.mem_image, not_exists, not_and]
    intro i hi hh
    have := hstrict i hi
    have h0 : rk (p 0) ≤ rk (p i.castSucc) := hmono _ _ (Fin.zero_le _)
    have := congrArg rk hh
    linarith

theorem pess_man (I : Instance n) {μ ν : Matching n} (hs : I.IsStable ν)
    (hW : IsWomanOptimal I μ) (v : Fin n) : I.manRank v (ν v) ≤ I.manRank v (μ v) := by
  by_contra hcon
  push_neg at hcon
  have hne : ν.symm (μ v) ≠ v := by
    intro h
    have : ν v = μ v := ((Equiv.symm_apply_eq ν).mp h).symm
    rw [this] at hcon
    exact lt_irrefl _ hcon
  have h2 := hW.2 ν hs (μ v)
  have h3 : μ.symm (μ v) = v := by simp
  rw [h3] at h2
  have h4 : I.womanRank (μ v) v < I.womanRank (μ v) (ν.symm (μ v)) :=
    lt_of_le_of_ne h2 (fun h => hne ((I.womanRank (μ v)).injective h).symm)
  exact hs v (μ v) ⟨hcon, h4⟩

theorem pess_woman (I : Instance n) {μ ν : Matching n} (hs : I.IsStable ν)
    (hM : IsManOptimal I μ) (w : Fin n) :
    I.womanRank w (ν.symm w) ≤ I.womanRank w (μ.symm w) := by
  by_contra hcon
  push_neg at hcon
  have hne : ν (μ.symm w) ≠ w := by
    intro h
    have : ν.symm w = μ.symm w := ((Equiv.eq_symm_apply ν).mpr h).symm
    rw [this] at hcon
    exact lt_irrefl _ hcon
  have h2 := hM.2 ν hs (μ.symm w)
  have h3 : μ (μ.symm w) = w := by simp
  rw [h3] at h2
  have h4 : I.manRank (μ.symm w) w < I.manRank (μ.symm w) (ν (μ.symm w)) :=
    lt_of_le_of_ne h2 (fun h => hne ((I.manRank (μ.symm w)).injective h).symm)
  exact hs (μ.symm w) w ⟨h4, hcon⟩

theorem stable_chain (Q : Member n) (m : Fin (Q.R + 1)) : Q.I.IsStable (Q.μ m) := by
  refine Fin.cases ?_ (fun i => ?_) m
  · exact Q.chain.1.1
  · exact (Q.chain.2.2 i).2.1

theorem mem_manPartners {I : Instance n} {v w : Fin n} :
    w ∈ manPartners I v ↔ ∃ μ : Matching n, I.IsStable μ ∧ μ v = w := by
  unfold manPartners
  simp

theorem mem_womanPartners {I : Instance n} {v w : Fin n} :
    w ∈ womanPartners I v ↔ ∃ μ : Matching n, I.IsStable μ ∧ μ.symm v = w := by
  unfold womanPartners
  simp

theorem deg_man (Q : Member n) (v : Fin n) : Q.deg .man v + 1 = (manPartners Q.I v).card := by
  obtain ⟨-, hchain, hstep⟩ := proposition_2_3 Q.I
  obtain ⟨rot, hrot, -, -, -⟩ := hchain Q.μ Q.chain
  have hst : ∀ i : Fin Q.R, ∀ v, Q.μ i.castSucc v ≠ Q.μ i.succ v →
      Q.μ i.succ v ∈ manPartners Q.I v ∧ Q.I.manPrefers v (Q.μ i.castSucc v) (Q.μ i.succ v) ∧
        ∀ w ∈ manPartners Q.I v, ¬ (Q.I.manPrefers v (Q.μ i.castSucc v) w ∧
          Q.I.manPrefers v w (Q.μ i.succ v)) := fun i =>
    (hstep _ _ _ (hrot i).1 (hrot i).2).1
  have key := card_P (manPartners Q.I v) Q.R (fun m => Q.μ m v) (fun x => (Q.I.manRank v x : ℤ))
    (fun a b hab => (Q.I.manRank v).injective (Fin.ext (by
      have hab' : ((Q.I.manRank v a : ℕ) : ℤ) = ((Q.I.manRank v b : ℕ) : ℤ) := hab
      exact_mod_cast hab')))
    (fun m => mem_manPartners.mpr ⟨Q.μ m, stable_chain Q m, rfl⟩)
    (fun i => by
      by_cases h : Q.μ i.castSucc v = Q.μ i.succ v
      · exact Or.inl h
      · right
        have := (hst i v h).2.1
        unfold Instance.manPrefers at this
        exact_mod_cast this)
    (fun i hne w hw hlt => by
      apply (hst i v hne).2.2 w hw
      unfold Instance.manPrefers
      constructor
      · exact_mod_cast hlt.1
      · exact_mod_cast hlt.2)
    (fun w hw => by
      obtain ⟨ν, hν, rfl⟩ := mem_manPartners.mp hw
      constructor
      · exact_mod_cast Q.chain.1.2 ν hν v
      · exact_mod_cast pess_man Q.I hν Q.chain.2.1 v)
  rw [key]
  rfl

theorem deg_woman (Q : Member n) (w : Fin n) :
    Q.deg .woman w + 1 = (womanPartners Q.I w).card := by
  obtain ⟨-, hchain, hstep⟩ := proposition_2_3 Q.I
  obtain ⟨rot, hrot, -, -, -⟩ := hchain Q.μ Q.chain
  have hst : ∀ i : Fin Q.R, ∀ w, (Q.μ i.castSucc).symm w ≠ (Q.μ i.succ).symm w →
      (Q.μ i.succ).symm w ∈ womanPartners Q.I w ∧
        Q.I.womanPrefers w ((Q.μ i.succ).symm w) ((Q.μ i.castSucc).symm w) ∧
        ∀ v ∈ womanPartners Q.I w, ¬ (Q.I.womanPrefers w ((Q.μ i.succ).symm w) v ∧
          Q.I.womanPrefers w v ((Q.μ i.castSucc).symm w)) := fun i =>
    (hstep _ _ _ (hrot i).1 (hrot i).2).2
  have key := card_P (womanPartners Q.I w) Q.R (fun m => (Q.μ m).symm w)
    (fun x => -(Q.I.womanRank w x : ℤ))
    (fun a b hab => (Q.I.womanRank w).injective (Fin.ext (by
      have : (Q.I.womanRank w a : ℤ) = (Q.I.womanRank w b : ℤ) := by linarith
      exact_mod_cast this)))
    (fun m => mem_womanPartners.mpr ⟨Q.μ m, stable_chain Q m, rfl⟩)
    (fun i => by
      by_cases h : (Q.μ i.castSucc).symm w = (Q.μ i.succ).symm w
      · exact Or.inl h
      · right
        have := (hst i w h).2.1
        unfold Instance.womanPrefers at this
        have h' : (Q.I.womanRank w ((Q.μ i.succ).symm w) : ℤ) <
            (Q.I.womanRank w ((Q.μ i.castSucc).symm w) : ℤ) := by exact_mod_cast this
        linarith)
    (fun i hne v hv hlt => by
      apply (hst i w hne).2.2 v hv
      unfold Instance.womanPrefers
      constructor
      · have : (Q.I.womanRank w ((Q.μ i.succ).symm w) : ℤ) < (Q.I.womanRank w v : ℤ) := by
          linarith [hlt.2]
        exact_mod_cast this
      · have : (Q.I.womanRank w v : ℤ) < (Q.I.womanRank w ((Q.μ i.castSucc).symm w) : ℤ) := by
          linarith [hlt.1]
        exact_mod_cast this)
    (fun v hv => by
      obtain ⟨ν, hν, rfl⟩ := mem_womanPartners.mp hv
      constructor
      · have := pess_woman Q.I hν Q.chain.1 w
        have : (Q.I.womanRank w (ν.symm w) : ℤ) ≤ (Q.I.womanRank w ((Q.μ 0).symm w) : ℤ) := by
          exact_mod_cast this
        linarith
      · have := Q.chain.2.1.2 ν hν w
        have : (Q.I.womanRank w ((Q.μ (Fin.last Q.R)).symm w) : ℤ) ≤
            (Q.I.womanRank w (ν.symm w) : ℤ) := by exact_mod_cast this
        linarith)
  rw [key]
  rfl

end Dev.Deg

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.JNum

variable {n : ℕ}

open Classical in
theorem numStable_eq_J (Q : Member n) : numStable Q.I = Q.J := by
  obtain ⟨-, -, -, -, -, hnum⟩ := lemma_3_1 Q.I
  obtain ⟨rot, -, hinj, hrange, hle⟩ := lemma_3_2 Q
  rw [hnum]
  -- downsets of `Fin R` correspond to full downsets
  have hle' : ∀ a b : Fin Q.R, Q.le b a → b = a ∨ FullLT Q.I (rot b) (rot a) := by
    intro a b hba
    by_cases h : b = a
    · exact Or.inl h
    · exact Or.inr ((hle b a h).mp hba)
  have hequiv : ∀ K : Finset (Fin Q.R),
      Q.IsDownsetIn Finset.univ K ↔ IsFullDownset Q.I (rot '' (K : Set (Fin Q.R))) := by
    intro K
    constructor
    · rintro ⟨-, hK⟩
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, -, rfl⟩
        rw [← hrange]; exact ⟨a, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩ ρ hρ hlt
        rw [← hrange] at hρ
        obtain ⟨b, rfl⟩ := hρ
        have hba : b ≠ a := by
          intro h; subst h; exact hlt.1 rfl
        have : Q.le b a := (hle b a hba).mpr hlt
        exact ⟨b, hK a ha b (Finset.mem_univ _) this, rfl⟩
    · rintro ⟨-, hD⟩
      refine ⟨Finset.subset_univ _, fun a ha b _ hba => ?_⟩
      rcases hle' a b hba with rfl | hlt
      · exact ha
      · have := hD (rot a) ⟨a, ha, rfl⟩ (rot b) (by rw [← hrange]; exact ⟨b, rfl⟩) hlt
        obtain ⟨c, hc, hcb⟩ := this
        have := hinj hcb
        subst this
        exact hc
  set 𝒟 : Finset (Finset (Fin Q.R)) :=
    (Finset.univ : Finset (Fin Q.R)).powerset.filter fun D => Q.IsDownsetIn Finset.univ D with h𝒟
  have hset : {D : Set (Rot n) | IsFullDownset Q.I D} =
      (fun K : Finset (Fin Q.R) => rot '' (K : Set (Fin Q.R))) '' (𝒟 : Set (Finset (Fin Q.R))) := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, h𝒟, Finset.mem_filter,
      Finset.mem_powerset, Finset.subset_univ, true_and]
    constructor
    · intro hD
      refine ⟨Finset.univ.filter fun a => rot a ∈ D, ?_, ?_⟩
      · rw [hequiv]
        have : rot '' ((Finset.univ.filter fun a => rot a ∈ D : Finset (Fin Q.R)) : Set (Fin Q.R)) = D := by
          ext σ
          simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          constructor
          · rintro ⟨a, ha, rfl⟩; exact ha
          · intro hσ
            have : σ ∈ Pi Q.I := hD.1 hσ
            rw [← hrange] at this
            obtain ⟨a, rfl⟩ := this
            exact ⟨a, hσ, rfl⟩
        rw [this]; exact hD
      · ext σ
        simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        constructor
        · rintro ⟨a, ha, rfl⟩; exact ha
        · intro hσ
          have : σ ∈ Pi Q.I := hD.1 hσ
          rw [← hrange] at this
          obtain ⟨a, rfl⟩ := this
          exact ⟨a, hσ, rfl⟩
    · rintro ⟨K, hK, rfl⟩
      exact (hequiv K).mp hK
  rw [hset, Set.ncard_image_of_injective, Set.ncard_coe_finset]
  · rfl
  · intro K₁ K₂ h
    apply Finset.coe_injective
    exact Set.image_injective.mpr hinj h

end Dev.JNum

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.JLe

variable {n : ℕ}

theorem J_zero (Q : Member n) (hR : Q.R = 0) : Q.J = 1 := by
  haveI : IsEmpty (Fin Q.R) := ⟨fun i => by have := i.2; omega⟩
  unfold Member.J Member.Jon
  rw [Finset.univ_eq_empty]
  simp [Member.IsDownsetIn]

/-- every member satisfies `J ≤ e^F`, from the branching property of `F_h` (Theorem 2) -/
theorem J_le_exp (h : ℕ → ℝ) (hh : IsAdmissible h) :
    ∀ (k : ℕ) (Q : Member n), Q.R = k → (Q.J : ℝ) ≤ Real.exp (Q.Fh h) := by
  have hb := theorem_2 (n := n) h hh
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Q hQ
    by_cases hR : Q.R = 0
    · have hF : Q.Fh h = 0 := hb.2.2.1 Q hR
      rw [J_zero Q hR, hF]
      simp
    · obtain ⟨a₁, a₂, h1, h2, hJ, hF⟩ := hb.2.2.2 Q hR
      have i1 := ih a₁.R (by simp only at h1; omega) a₁ rfl
      have i2 := ih a₂.R (by simp only at h2; omega) a₂ rfl
      have hJ' : (Q.J : ℝ) = (a₁.J : ℝ) + (a₂.J : ℝ) := by
        have : Q.J = a₁.J + a₂.J := hJ
        exact_mod_cast this
      rw [hJ']
      exact (add_le_add i1 i2).trans hF

end Dev.JLe

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.T1

variable {n : ℕ}

theorem sum_Icc_eq_range (g : ℕ → ℝ) (m : ℕ) :
    ∑ d ∈ Finset.Icc 1 m, g d = ∑ i ∈ Finset.range m, g (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem W_le_tsum (h : ℕ → ℝ) (hpos : ∀ d, 1 ≤ d → 0 < h d)
    (hsum : Summable (fun d => h (d + 1))) (d : ℕ) :
    ∑ r ∈ Finset.Icc 1 d, h r ≤ ∑' d, h (d + 1) := by
  rw [sum_Icc_eq_range]
  exact hsum.sum_le_tsum _ (fun i _ => (hpos (i + 1) (by omega)).le)

theorem sum_dL (Q : Member n) (f : ℕ → ℝ) (s : Sex) :
    ∑ v : Fin n, f (Q.dL s v) = ∑ p : Fin n, f (Q.deg s p) := by
  cases s
  · rfl
  · exact Equiv.sum_comp (Q.μ 0) (fun p => f (Q.deg .woman p))

theorem count_le (h : ℕ → ℝ) (hh : IsAdmissible h) (I : Instance n) :
    (numStable I : ℝ) ≤ Real.exp ((1 / 2) * ∑ v : Fin n,
      (∑ d ∈ Finset.Icc 1 (Dm I v - 1), h d + ∑ d ∈ Finset.Icc 1 (Dw I v - 1), h d)) := by
  obtain ⟨hA, hB, hC, hD, hN, hle⟩ := proposition_2_5 I
  obtain ⟨R, μ, hch⟩ := Dev.Chain.exists_chain (normalize I)
  let Q : Member n := ⟨normalize I, R, μ, hN, hch⟩
  have hJ : numStable (normalize I) = Q.J := Dev.JNum.numStable_eq_J Q
  have h1 : (numStable I : ℝ) ≤ Q.J := by
    have : numStable I ≤ Q.J := hJ ▸ hle
    exact_mod_cast this
  refine h1.trans ((Dev.JLe.J_le_exp h hh _ Q rfl).trans (le_of_eq ?_))
  congr 1
  unfold Member.Fh
  rw [Finset.sum_add_distrib, sum_dL Q (W h) .man, sum_dL Q (W h) .woman, ← Finset.sum_add_distrib]
  congr 2
  funext p
  have e1 : Q.deg .man p = Dm I p - 1 := by
    have := Dev.Deg.deg_man Q p
    have e : (manPartners (normalize I) p) = manPartners I p := hB p
    show Q.deg .man p = (manPartners I p).card - 1
    rw [← e]
    simp only [Q] at this ⊢
    omega
  have e2 : Q.deg .woman p = Dw I p - 1 := by
    have := Dev.Deg.deg_woman Q p
    have e : (womanPartners (normalize I) p) = womanPartners I p := hC p
    show Q.deg .woman p = (womanPartners I p).card - 1
    rw [← e]
    simp only [Q] at this ⊢
    omega
  rw [e1, e2]
  rfl

end Dev.T1

theorem chk_theorem_1 :
    ∃ h : ℕ → ℝ, (∀ d, 1 ≤ d → 0 < h d) ∧ Summable (fun d => h (d + 1)) ∧
      ∑' d, h (d + 1) < Real.log 2.81 ∧
      ∀ n : ℕ, 1 ≤ n →
        (∀ I : Instance n,
          (numStable I : ℝ) ≤ Real.exp ((1 / 2) * ∑ v : Fin n,
            (∑ d ∈ Finset.Icc 1 (Dm I v - 1), h d + ∑ d ∈ Finset.Icc 1 (Dw I v - 1), h d))) ∧
        (SM n : ℝ) ≤ Real.exp ((n : ℝ) * ∑ d ∈ Finset.Icc 1 (n - 1), h d) ∧
        Real.exp ((n : ℝ) * ∑ d ∈ Finset.Icc 1 (n - 1), h d) < 2.81 ^ n := by
  obtain ⟨h, hadm, hsum, hlt⟩ := theorem_3
  have hpos := hadm.1
  refine ⟨h, hpos, hsum, hlt, fun n hn => ⟨fun I => Dev.T1.count_le h hadm I, ?_, ?_⟩⟩
  · -- the maximum
    have hne : (Set.range (numStable (n := n))).Nonempty :=
      ⟨_, ⟨⟨fun _ => Equiv.refl _, fun _ => Equiv.refl _⟩, rfl⟩⟩
    have hbdd : BddAbove (Set.range (numStable (n := n))) := by
      refine ⟨Fintype.card (Matching n), ?_⟩
      rintro _ ⟨I, rfl⟩
      exact Fintype.card_subtype_le _
    obtain ⟨I, hI⟩ := Nat.sSup_mem hne hbdd
    have hSM : SM n = numStable I := hI.symm
    rw [hSM]
    refine (Dev.T1.count_le h hadm I).trans (Real.exp_le_exp.mpr ?_)
    have hmono : ∀ k, k ≤ n - 1 → ∑ d ∈ Finset.Icc 1 k, h d ≤ ∑ d ∈ Finset.Icc 1 (n - 1), h d := by
      intro k hk
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hk)
        (fun d hd _ => (hpos d (Finset.mem_Icc.mp hd).1).le)
    have hDm : ∀ v, Dm I v - 1 ≤ n - 1 := fun v => by
      have : (manPartners I v).card ≤ n := by
        simpa using Finset.card_le_univ (manPartners I v)
      unfold Dm; omega
    have hDw : ∀ v, Dw I v - 1 ≤ n - 1 := fun v => by
      have : (womanPartners I v).card ≤ n := by
        simpa using Finset.card_le_univ (womanPartners I v)
      unfold Dw; omega
    calc (1 / 2 : ℝ) * ∑ v : Fin n, (∑ d ∈ Finset.Icc 1 (Dm I v - 1), h d +
          ∑ d ∈ Finset.Icc 1 (Dw I v - 1), h d)
        ≤ (1 / 2 : ℝ) * ∑ v : Fin n, (∑ d ∈ Finset.Icc 1 (n - 1), h d +
          ∑ d ∈ Finset.Icc 1 (n - 1), h d) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum fun v _ => add_le_add (hmono _ (hDm v)) (hmono _ (hDw v))
      _ = (n : ℝ) * ∑ d ∈ Finset.Icc 1 (n - 1), h d := by
          simp
          ring
  · have hW := Dev.T1.W_le_tsum h hpos hsum (n - 1)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc Real.exp ((n : ℝ) * ∑ d ∈ Finset.Icc 1 (n - 1), h d)
        < Real.exp ((n : ℝ) * Real.log 2.81) := by
          apply Real.exp_lt_exp.mpr
          exact mul_lt_mul_of_pos_left (lt_of_le_of_lt hW hlt) hnpos
      _ = 2.81 ^ n := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

end StableCount
end

theorem solution : type_of% @StableCount.chk_theorem_1 := @StableCount.chk_theorem_1
