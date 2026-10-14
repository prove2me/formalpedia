-- Prove2me | solution 1 for StableMatching.stable_matchings_distribLattice
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T15:14:29.947918+00:00
-- url     : https://prove2.me/submissions/e0be2a3f-584f-4fba-b49c-c86665bd55f7

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

set_option autoImplicit false

open StableMatching

namespace StableMatching.GSLat

variable {n : ℕ} (I : Instance n)

/-- (K1) If `m` strictly prefers `μ m` to `ν m` and `ν` is stable, then `w := μ m` strictly prefers
her `ν`-partner to `m`. -/
theorem K1 {μ ν : Matching n} (hν : I.IsStable ν) {m : Fin n}
    (h : I.manRank m (μ m) < I.manRank m (ν m)) :
    I.womanRank (μ m) (ν.symm (μ m)) < I.womanRank (μ m) m := by
  have hb := hν m (μ m)
  unfold Instance.IsBlockingPair Instance.manPrefers Instance.womanPrefers at hb
  have h1 : I.womanRank (μ m) (ν.symm (μ m)) ≤ I.womanRank (μ m) m := by
    by_contra h2
    exact hb ⟨h, lt_of_not_ge h2⟩
  have hne : ν.symm (μ m) ≠ m := by
    intro he
    have : ν m = μ m := (ν.symm_apply_eq.1 he).symm
    rw [this] at h
    exact lt_irrefl _ h
  exact lt_of_le_of_ne h1 (fun he => hne ((I.womanRank (μ m)).injective (Fin.ext (congrArg Fin.val he))))

/-- (K3) If `μ, ν` are stable and `m` strictly prefers `μ m` to `ν m`, then `w := ν m` strictly
prefers `m` to her `μ`-partner. Proved by the counting argument (K2). -/
theorem K3 {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) {m : Fin n}
    (h : I.manRank m (μ m) < I.manRank m (ν m)) :
    I.womanRank (ν m) m < I.womanRank (ν m) (μ.symm (ν m)) := by
  classical
  let M : Finset (Fin n) :=
    Finset.univ.filter (fun m => I.manRank m (μ m) < I.manRank m (ν m))
  let W : Finset (Fin n) :=
    Finset.univ.filter (fun w => I.womanRank w (ν.symm w) < I.womanRank w (μ.symm w))
  have h1 : M.image μ ⊆ W := by
    intro w hw
    simp only [Finset.mem_image, M, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨m, hm, rfl⟩ := hw
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact K1 I hν hm
  have h2 : W ⊆ M.image ν := by
    intro w hw
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_image, M, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨ν.symm w, ?_, by simp⟩
    have hb := hμ (ν.symm w) w
    unfold Instance.IsBlockingPair Instance.manPrefers Instance.womanPrefers at hb
    simp only [Equiv.apply_symm_apply]
    have hle : I.manRank (ν.symm w) (μ (ν.symm w)) ≤ I.manRank (ν.symm w) w := by
      by_contra h3
      exact hb ⟨lt_of_not_ge h3, hw⟩
    refine lt_of_le_of_ne hle ?_
    intro he
    have he' : μ (ν.symm w) = w := (I.manRank (ν.symm w)).injective he
    have : μ.symm w = ν.symm w := μ.symm_apply_eq.2 he'.symm
    rw [this] at hw
    exact lt_irrefl _ hw
  have hcard : (M.image ν).card ≤ (M.image μ).card := by
    rw [Finset.card_image_of_injective _ ν.injective,
      Finset.card_image_of_injective _ μ.injective]
  have heq : M.image μ = M.image ν := Finset.eq_of_subset_of_card_le (h1.trans h2) hcard
  have hmem : ν m ∈ M.image μ := by
    rw [heq]
    exact Finset.mem_image_of_mem _ (by simp [M, h])
  obtain ⟨m'', hm'', he⟩ := Finset.mem_image.1 hmem
  have hm2 : I.manRank m'' (μ m'') < I.manRank m'' (ν m'') := by simpa [M] using hm''
  have hk := K1 I hν hm2
  rw [he] at hk
  simp only [Equiv.symm_apply_apply] at hk
  have hs : μ.symm (ν m) = m'' := by rw [← he]; simp
  rw [hs]
  exact hk

/-- The man-better choice. -/
def lamF (μ ν : Matching n) (m : Fin n) : Fin n :=
  if I.manRank m (μ m) ≤ I.manRank m (ν m) then μ m else ν m

/-- The man-worse choice. -/
def rhoF (μ ν : Matching n) (m : Fin n) : Fin n :=
  if I.manRank m (μ m) ≤ I.manRank m (ν m) then ν m else μ m

theorem rank_lamF (μ ν : Matching n) (m : Fin n) :
    I.manRank m (lamF I μ ν m) = min (I.manRank m (μ m)) (I.manRank m (ν m)) := by
  unfold lamF
  rw [min_def]
  split_ifs <;> rfl

theorem rank_rhoF (μ ν : Matching n) (m : Fin n) :
    I.manRank m (rhoF I μ ν m) = max (I.manRank m (μ m)) (I.manRank m (ν m)) := by
  unfold rhoF
  rw [max_def]
  split_ifs <;> rfl

theorem lamF_injective {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    Function.Injective (lamF I μ ν) := by
  -- mixed case: `m1` takes `μ m1` (weakly better), `m2` takes `ν m2` (strictly better)
  have key : ∀ {μ ν : Matching n}, I.IsStable μ → I.IsStable ν → ∀ m1 m2 : Fin n,
      I.manRank m1 (μ m1) ≤ I.manRank m1 (ν m1) → I.manRank m2 (ν m2) < I.manRank m2 (μ m2) →
      μ m1 = ν m2 → m1 = m2 := by
    intro μ ν hμ hν m1 m2 h1 h2 he
    by_cases hc : μ m1 = ν m1
    · rw [hc] at he; exact ν.injective he
    · exfalso
      have h1' : I.manRank m1 (μ m1) < I.manRank m1 (ν m1) :=
        lt_of_le_of_ne h1 (fun h => hc ((I.manRank m1).injective h))
      have ha := K1 I hν h1'
      have hb := K1 I hμ h2
      rw [he] at ha
      simp only [Equiv.symm_apply_apply] at ha hb
      have : μ.symm (ν m2) = m1 := by rw [← he]; simp
      rw [this] at hb
      exact lt_asymm ha hb
  intro m1 m2 he
  unfold lamF at he
  split_ifs at he with h1 h2 h2
  · exact μ.injective he
  · exact key hμ hν m1 m2 h1 (lt_of_not_ge h2) he
  · exact (key hμ hν m2 m1 h2 (lt_of_not_ge h1) he.symm).symm
  · exact ν.injective he

theorem rhoF_injective {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    Function.Injective (rhoF I μ ν) := by
  -- mixed case: `m1` takes `ν m1` (weakly worse), `m2` takes `μ m2` (strictly worse)
  have key : ∀ {μ ν : Matching n}, I.IsStable μ → I.IsStable ν → ∀ m1 m2 : Fin n,
      I.manRank m1 (μ m1) ≤ I.manRank m1 (ν m1) → I.manRank m2 (ν m2) < I.manRank m2 (μ m2) →
      ν m1 = μ m2 → m1 = m2 := by
    intro μ ν hμ hν m1 m2 h1 h2 he
    by_cases hc : μ m1 = ν m1
    · rw [← hc] at he; exact μ.injective he
    · exfalso
      have h1' : I.manRank m1 (μ m1) < I.manRank m1 (ν m1) :=
        lt_of_le_of_ne h1 (fun h => hc ((I.manRank m1).injective h))
      have ha := K3 I hμ hν h1'
      have hb := K3 I hν hμ h2
      rw [he] at ha
      simp only [Equiv.symm_apply_apply] at ha hb
      have : ν.symm (μ m2) = m1 := by rw [← he]; simp
      rw [this] at hb
      exact lt_asymm ha hb
  intro m1 m2 he
  unfold rhoF at he
  split_ifs at he with h1 h2 h2
  · exact ν.injective he
  · exact key hμ hν m1 m2 h1 (lt_of_not_ge h2) he
  · exact (key hμ hν m2 m1 h2 (lt_of_not_ge h1) he.symm).symm
  · exact μ.injective he

theorem lam_stable {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (σ : Matching n) (hσ : ∀ m, σ m = lamF I μ ν m) : I.IsStable σ := by
  intro m w hbl
  obtain ⟨h1, h2⟩ := hbl
  unfold Instance.manPrefers at h1
  unfold Instance.womanPrefers at h2
  rw [hσ, rank_lamF, lt_min_iff] at h1
  have hm' : lamF I μ ν (σ.symm w) = w := by rw [← hσ]; simp
  unfold lamF at hm'
  split_ifs at hm' with hc
  · have : μ.symm w = σ.symm w := μ.symm_apply_eq.2 hm'.symm
    exact hμ m w ⟨h1.1, by unfold Instance.womanPrefers; rw [this]; exact h2⟩
  · have : ν.symm w = σ.symm w := ν.symm_apply_eq.2 hm'.symm
    exact hν m w ⟨h1.2, by unfold Instance.womanPrefers; rw [this]; exact h2⟩

/-- Core of stability of the man-worse matching. -/
theorem rho_stable_aux {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (σ : Matching n) (hσ : ∀ m, σ m = rhoF I μ ν m) (m w : Fin n)
    (h1 : I.manRank m w < I.manRank m (μ m))
    (h2 : I.womanRank w m < I.womanRank w (σ.symm w)) : False := by
  have hb := hμ m w
  unfold Instance.IsBlockingPair Instance.manPrefers Instance.womanPrefers at hb
  have h3 : I.womanRank w (μ.symm w) ≤ I.womanRank w m := by
    by_contra h4
    exact hb ⟨h1, lt_of_not_ge h4⟩
  have h5 : I.womanRank w (μ.symm w) < I.womanRank w (σ.symm w) := lt_of_le_of_lt h3 h2
  set m' := σ.symm w with hm'def
  have hm' : rhoF I μ ν m' = w := by rw [← hσ, hm'def]; simp
  have hne : μ m' ≠ w := by
    intro he
    have : μ.symm w = m' := by rw [← he]; simp
    rw [this] at h5
    exact lt_irrefl _ h5
  unfold rhoF at hm'
  split_ifs at hm' with hc
  · -- σ m' = ν m' = w and m' strictly prefers μ
    have hc' : I.manRank m' (μ m') < I.manRank m' (ν m') := by
      refine lt_of_le_of_ne hc ?_
      intro he
      exact hne (((I.manRank m').injective he).trans hm')
    have hk := K3 I hμ hν hc'
    rw [hm'] at hk
    exact lt_asymm hk h5
  · exact hne hm'

theorem rho_stable {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (σ : Matching n) (hσ : ∀ m, σ m = rhoF I μ ν m) : I.IsStable σ := by
  intro m w hbl
  obtain ⟨h1, h2⟩ := hbl
  unfold Instance.manPrefers at h1
  unfold Instance.womanPrefers at h2
  rw [hσ, rank_rhoF, lt_max_iff] at h1
  rcases h1 with h1 | h1
  · exact rho_stable_aux I hμ hν σ hσ m w h1 h2
  · have hσ' : ∀ m, σ m = rhoF I ν μ m := by
      intro m
      rw [hσ]
      unfold rhoF
      split_ifs with ha hb hb
      · exact (I.manRank m).injective (le_antisymm hb ha)
      · rfl
      · rfl
      · exact absurd (le_of_lt (lt_of_not_ge ha)) hb
    exact rho_stable_aux I hν hμ σ hσ' m w h1 h2


/-- Rank vector of a stable matching. -/
def rk (μ : {μ : Matching n // I.IsStable μ}) : Fin n → Fin n := fun m => I.manRank m (μ.1 m)

theorem rk_injective : Function.Injective (rk I) := by
  intro μ ν h
  apply Subtype.ext
  apply Equiv.ext
  intro m
  exact (I.manRank m).injective (congrFun h m)

/-- The man-better matching (meet). -/
noncomputable def meetS (μ ν : {μ : Matching n // I.IsStable μ}) :
    {μ : Matching n // I.IsStable μ} :=
  ⟨Equiv.ofBijective (lamF I μ.1 ν.1)
      (Finite.injective_iff_bijective.1 (lamF_injective I μ.2 ν.2)),
    lam_stable I μ.2 ν.2 _ (fun _ => rfl)⟩

/-- The man-worse matching (join). -/
noncomputable def joinS (μ ν : {μ : Matching n // I.IsStable μ}) :
    {μ : Matching n // I.IsStable μ} :=
  ⟨Equiv.ofBijective (rhoF I μ.1 ν.1)
      (Finite.injective_iff_bijective.1 (rhoF_injective I μ.2 ν.2)),
    rho_stable I μ.2 ν.2 _ (fun _ => rfl)⟩

theorem rk_meetS (μ ν : {μ : Matching n // I.IsStable μ}) :
    rk I (meetS I μ ν) = rk I μ ⊓ rk I ν := by
  funext m
  show I.manRank m (lamF I μ.1 ν.1 m) = _
  rw [rank_lamF]
  rfl

theorem rk_joinS (μ ν : {μ : Matching n // I.IsStable μ}) :
    rk I (joinS I μ ν) = rk I μ ⊔ rk I ν := by
  funext m
  show I.manRank m (rhoF I μ.1 ν.1 m) = _
  rw [rank_rhoF]
  rfl

end StableMatching.GSLat

open StableMatching.GSLat in
theorem solution {n : ℕ} (I : Instance n) :
    ∃ L : DistribLattice {μ : Matching n // I.IsStable μ},
      ∀ μ ν : {μ : Matching n // I.IsStable μ},
        L.le μ ν ↔ ∀ m : Fin n, I.manRank m (μ.1 m) ≤ I.manRank m (ν.1 m) := by
  letI : Max {μ : Matching n // I.IsStable μ} := ⟨joinS I⟩
  letI : Min {μ : Matching n // I.IsStable μ} := ⟨meetS I⟩
  letI : LE {μ : Matching n // I.IsStable μ} := ⟨fun a b => rk I a ≤ rk I b⟩
  letI : LT {μ : Matching n // I.IsStable μ} := ⟨fun a b => rk I a < rk I b⟩
  refine ⟨Function.Injective.distribLattice (rk I) (rk_injective I) Iff.rfl Iff.rfl
    (rk_joinS I) (rk_meetS I), ?_⟩
  intro μ ν
  exact Pi.le_def
