-- Prove2me | solution 1 for TheoryOfGames.GeneralGames.restrictedCharFun_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:20:22.279608+00:00
-- url     : https://prove2.me/submissions/6d91e38b-2c77-46bb-b7bd-99ffc6ece30a

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

set_option autoImplicit false

namespace P57dc

open TheoryOfGames.GeneralGames TheoryOfGames.GeneralGames.GeneralGame

variable {n : ℕ} (Γ : GeneralGame n)

/-- Real members of the image of `S ⊆ I` in `Ī`. -/
abbrev RP (S : Finset (Fin n)) : Finset (Fin n) := realPart (S.map Fin.castSuccEmb)

theorem mem_RP (S : Finset (Fin n)) (k : Fin n) : k ∈ RP S ↔ k ∈ S := by
  change k ∈ Finset.univ.filter (fun i : Fin n => Fin.castSucc i ∈ S.map Fin.castSuccEmb) ↔ _
  simp

theorem smk {X : Type} [Fintype X] (f : X → ℝ) (h : f ∈ stdSimplex ℝ X) (x : X) :
    (⟨f, h⟩ : stdSimplex ℝ X) x = f x := rfl

theorem mem_RPc (S : Finset (Fin n)) (k : Fin n) : k ∈ (RP S)ᶜ ↔ k ∉ S := by
  rw [Finset.mem_compl, mem_RP]

/-- Restriction of an aggregate to a smaller set of players. -/
def res {A B : Finset (Fin n)} (h : ∀ k, k ∈ A → k ∈ B) (c : Γ.CoalStrat B) : Γ.CoalStrat A :=
  fun k => c ⟨k.1, h _ k.2⟩

/-- Restriction of a full profile to a set of players. -/
def rO (A : Finset (Fin n)) (τ : (k : Fin n) → Fin (Γ.β k)) : Γ.CoalStrat A :=
  fun k => τ k.1

def splitEquiv {A B R : Finset (Fin n)} (hR : ∀ k, k ∈ R ↔ k ∈ A ∨ k ∈ B)
    (hd : ∀ k, k ∈ A → k ∉ B) : Γ.CoalStrat R ≃ Γ.CoalStrat A × Γ.CoalStrat B where
  toFun c := (res Γ (fun k hk => (hR k).2 (Or.inl hk)) c, res Γ (fun k hk => (hR k).2 (Or.inr hk)) c)
  invFun p := fun k =>
    if h : k.1 ∈ A then p.1 ⟨k.1, h⟩ else p.2 ⟨k.1, ((hR k.1).1 k.2).resolve_left h⟩
  left_inv c := by
    funext k
    by_cases h : k.1 ∈ A <;> simp [h, res]
  right_inv p := by
    rcases p with ⟨a, b⟩
    refine Prod.ext ?_ ?_
    · funext k
      simp [res, k.2]
    · funext k
      have : k.1 ∉ A := fun h => hd _ h k.2
      simp [res, this]

theorem sum_split {A B R : Finset (Fin n)} (hR : ∀ k, k ∈ R ↔ k ∈ A ∨ k ∈ B)
    (hd : ∀ k, k ∈ A → k ∉ B) (h1 : ∀ k, k ∈ A → k ∈ R) (h2 : ∀ k, k ∈ B → k ∈ R)
    (f : Γ.CoalStrat A → ℝ) (g : Γ.CoalStrat B → ℝ) :
    ∑ c : Γ.CoalStrat R, f (res Γ h1 c) * g (res Γ h2 c) = (∑ a, f a) * (∑ b, g b) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (splitEquiv Γ hR hd) _ (fun p => f p.1 * g p.2) (fun c => rfl)

def fullEquiv (R : Finset (Fin n)) :
    ((k : Fin n) → Fin (Γ.β k)) ≃ Γ.CoalStrat R × Γ.CoalStrat Rᶜ where
  toFun τ := (rO Γ R τ, rO Γ Rᶜ τ)
  invFun p := Γ.joint R p.1 p.2
  left_inv τ := by
    funext k
    by_cases h : k ∈ R <;> simp [joint, rO, h]
  right_inv p := by
    rcases p with ⟨a, b⟩
    refine Prod.ext ?_ ?_
    · funext k
      simp [joint, rO, k.2]
    · funext k
      have : k.1 ∉ R := Finset.mem_compl.1 k.2
      simp [joint, rO, this]

theorem bilin_eq (S : Finset (Fin n)) (ξ : Γ.CoalStrat (RP S) → ℝ)
    (η : Γ.CoalStrat (RP S)ᶜ → ℝ) :
    Γ.bilin (S.map Fin.castSuccEmb) ξ η =
      ∑ τ, (∑ k ∈ S, Γ.H τ k) * ξ (rO Γ (RP S) τ) * η (rO Γ (RP S)ᶜ τ) := by
  unfold bilin
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_equiv (fullEquiv Γ (RP S)) _
    (fun p => Γ.coalPayoff (S.map Fin.castSuccEmb) p.1 p.2 * ξ p.1 * η p.2) (fun τ => ?_)
  have hj : Γ.joint (RP S) (rO Γ (RP S) τ) (rO Γ (RP S)ᶜ τ) = τ :=
    (fullEquiv Γ (RP S)).left_inv τ
  simp only [fullEquiv, Equiv.coe_fn_mk, coalPayoff]
  rw [hj]
  simp [Finset.sum_map, extH]

theorem bilin_abs_le (S' : Finset (Fin (n + 1)))
    (ξ : stdSimplex ℝ (Γ.CoalStrat (realPart S')))
    (η : stdSimplex ℝ (Γ.CoalStrat (realPart S')ᶜ)) :
    |Γ.bilin S' ξ η| ≤ ∑ a, ∑ b, |Γ.coalPayoff S' a b| := by
  unfold bilin
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (stdSimplex.zero_le ξ a),
    abs_of_nonneg (stdSimplex.zero_le η b)]
  exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (stdSimplex.zero_le ξ a))
    (stdSimplex.le_one η b)).trans (mul_le_of_le_one_right (abs_nonneg _) (stdSimplex.le_one ξ a))

theorem ne_simplex (R : Finset (Fin n)) : Nonempty (stdSimplex ℝ (Γ.CoalStrat R)) :=
  ⟨⟨_, single_mem_stdSimplex ℝ ((fun k => ⟨0, Γ.β_pos k⟩) : Γ.CoalStrat R)⟩⟩

theorem bddBelow_inner (S' : Finset (Fin (n + 1)))
    (ξ : stdSimplex ℝ (Γ.CoalStrat (realPart S'))) :
    BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat (realPart S')ᶜ) =>
      Γ.bilin S' ξ η) := by
  refine ⟨-(∑ a, ∑ b, |Γ.coalPayoff S' a b|), ?_⟩
  rintro _ ⟨η, rfl⟩
  exact (abs_le.1 (bilin_abs_le Γ S' ξ η)).1

theorem bddAbove_outer (S' : Finset (Fin (n + 1))) :
    BddAbove (Set.range fun ξ : stdSimplex ℝ (Γ.CoalStrat (realPart S')) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat (realPart S')ᶜ), Γ.bilin S' ξ η) := by
  refine ⟨∑ a, ∑ b, |Γ.coalPayoff S' a b|, ?_⟩
  rintro _ ⟨ξ, rfl⟩
  obtain ⟨η0⟩ := ne_simplex Γ (realPart S')ᶜ
  exact (ciInf_le (bddBelow_inner Γ S' ξ) η0).trans (abs_le.1 (bilin_abs_le Γ S' ξ η0)).2

theorem res_rO {A B : Finset (Fin n)} (h : ∀ k, k ∈ A → k ∈ B) (τ : (k : Fin n) → Fin (Γ.β k)) :
    res Γ h (rO Γ B τ) = rO Γ A τ := rfl

theorem split_bilin (S T : Finset (Fin n)) (hST : Disjoint S T)
    (ξS : Γ.CoalStrat (RP S) → ℝ) (ξT : Γ.CoalStrat (RP T) → ℝ)
    (ξU : Γ.CoalStrat (RP (S ∪ T)) → ℝ) (η : Γ.CoalStrat (RP (S ∪ T))ᶜ → ℝ)
    (ηS : Γ.CoalStrat (RP S)ᶜ → ℝ) (ηT : Γ.CoalStrat (RP T)ᶜ → ℝ)
    (hSU : ∀ k, k ∈ RP S → k ∈ RP (S ∪ T)) (hTU : ∀ k, k ∈ RP T → k ∈ RP (S ∪ T))
    (a1 : ∀ k, k ∈ RP T → k ∈ (RP S)ᶜ) (a2 : ∀ k, k ∈ (RP (S ∪ T))ᶜ → k ∈ (RP S)ᶜ)
    (b1 : ∀ k, k ∈ RP S → k ∈ (RP T)ᶜ) (b2 : ∀ k, k ∈ (RP (S ∪ T))ᶜ → k ∈ (RP T)ᶜ)
    (hU : ∀ σ, ξU σ = ξS (res Γ hSU σ) * ξT (res Γ hTU σ))
    (hS : ∀ c, ηS c = ξT (res Γ a1 c) * η (res Γ a2 c))
    (hT : ∀ c, ηT c = ξS (res Γ b1 c) * η (res Γ b2 c)) :
    Γ.bilin ((S ∪ T).map Fin.castSuccEmb) ξU η =
      Γ.bilin (S.map Fin.castSuccEmb) ξS ηS + Γ.bilin (T.map Fin.castSuccEmb) ξT ηT := by
  rw [bilin_eq, bilin_eq, bilin_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_union hST, hU, hS, hT]
  simp only [res_rO]
  ring

theorem key (S T : Finset (Fin n)) (hST : Disjoint S T)
    (ξS : stdSimplex ℝ (Γ.CoalStrat (RP S))) (ξT : stdSimplex ℝ (Γ.CoalStrat (RP T))) :
    (⨅ η : stdSimplex ℝ (Γ.CoalStrat (RP S)ᶜ), Γ.bilin (S.map Fin.castSuccEmb) ξS η) +
      (⨅ η : stdSimplex ℝ (Γ.CoalStrat (RP T)ᶜ), Γ.bilin (T.map Fin.castSuccEmb) ξT η) ≤
      Γ.extCharFun ((S ∪ T).map Fin.castSuccEmb) := by
  have hd := Finset.disjoint_left.1 hST
  have hSU : ∀ k, k ∈ RP S → k ∈ RP (S ∪ T) := by
    intro k; simp only [mem_RP, Finset.mem_union]; tauto
  have hTU : ∀ k, k ∈ RP T → k ∈ RP (S ∪ T) := by
    intro k; simp only [mem_RP, Finset.mem_union]; tauto
  have hpU : ∀ k, k ∈ RP (S ∪ T) ↔ k ∈ RP S ∨ k ∈ RP T := by
    intro k; simp only [mem_RP, Finset.mem_union]
  have hdU : ∀ k, k ∈ RP S → k ∉ RP T := by
    intro k; simp only [mem_RP]; exact fun h => hd h
  let ξU : stdSimplex ℝ (Γ.CoalStrat (RP (S ∪ T))) :=
    ⟨fun σ => ξS (res Γ hSU σ) * ξT (res Γ hTU σ),
      fun σ => mul_nonneg (stdSimplex.zero_le ξS _) (stdSimplex.zero_le ξT _),
      by rw [sum_split Γ hpU hdU hSU hTU, stdSimplex.sum_eq_one, stdSimplex.sum_eq_one, one_mul]⟩
  have := ne_simplex Γ (RP (S ∪ T))ᶜ
  refine le_trans ?_ (le_ciSup (bddAbove_outer Γ _) ξU)
  refine le_ciInf fun η => ?_
  -- the strategy of `I - S`: `T` plays `ξT`, `I - (S ∪ T)` plays `η`
  have a1 : ∀ k, k ∈ RP T → k ∈ (RP S)ᶜ := by
    intro k; simp only [mem_RP, mem_RPc]; intro h hk; exact hd hk h
  have a2 : ∀ k, k ∈ (RP (S ∪ T))ᶜ → k ∈ (RP S)ᶜ := by
    intro k; simp only [mem_RPc, Finset.mem_union]; tauto
  have apS : ∀ k, k ∈ (RP S)ᶜ ↔ k ∈ RP T ∨ k ∈ (RP (S ∪ T))ᶜ := by
    intro k; simp only [mem_RP, mem_RPc, Finset.mem_union]; tauto
  have adS : ∀ k, k ∈ RP T → k ∉ (RP (S ∪ T))ᶜ := by
    intro k; simp only [mem_RP, mem_RPc, Finset.mem_union]; tauto
  let ηS : stdSimplex ℝ (Γ.CoalStrat (RP S)ᶜ) :=
    ⟨fun c => ξT (res Γ a1 c) * η (res Γ a2 c),
      fun c => mul_nonneg (stdSimplex.zero_le ξT _) (stdSimplex.zero_le η _),
      by rw [sum_split Γ apS adS a1 a2, stdSimplex.sum_eq_one, stdSimplex.sum_eq_one, one_mul]⟩
  have b1 : ∀ k, k ∈ RP S → k ∈ (RP T)ᶜ := by
    intro k; simp only [mem_RP, mem_RPc]; exact fun h => hd h
  have b2 : ∀ k, k ∈ (RP (S ∪ T))ᶜ → k ∈ (RP T)ᶜ := by
    intro k; simp only [mem_RPc, Finset.mem_union]; tauto
  have bpT : ∀ k, k ∈ (RP T)ᶜ ↔ k ∈ RP S ∨ k ∈ (RP (S ∪ T))ᶜ := by
    intro k; simp only [mem_RP, mem_RPc, Finset.mem_union]
    constructor
    · intro h; by_cases hs : k ∈ S
      · exact Or.inl hs
      · exact Or.inr (by tauto)
    · rintro (h | h)
      · exact hd h
      · tauto
  have bdT : ∀ k, k ∈ RP S → k ∉ (RP (S ∪ T))ᶜ := by
    intro k; simp only [mem_RP, mem_RPc, Finset.mem_union]; tauto
  let ηT : stdSimplex ℝ (Γ.CoalStrat (RP T)ᶜ) :=
    ⟨fun c => ξS (res Γ b1 c) * η (res Γ b2 c),
      fun c => mul_nonneg (stdSimplex.zero_le ξS _) (stdSimplex.zero_le η _),
      by rw [sum_split Γ bpT bdT b1 b2, stdSimplex.sum_eq_one, stdSimplex.sum_eq_one, one_mul]⟩
  have e := split_bilin Γ S T hST ξS ξT ξU η ηS ηT hSU hTU a1 a2 b1 b2
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  rw [e]
  exact add_le_add (ciInf_le (bddBelow_inner Γ _ ξS) ηS) (ciInf_le (bddBelow_inner Γ _ ξT) ηT)

theorem superadd (S T : Finset (Fin n)) (hST : Disjoint S T) :
    Γ.restrictedCharFun S + Γ.restrictedCharFun T ≤ Γ.restrictedCharFun (S ∪ T) := by
  unfold restrictedCharFun
  have := ne_simplex Γ (RP S)
  have := ne_simplex Γ (RP T)
  rw [← le_sub_iff_add_le]
  refine ciSup_le fun ξS => ?_
  rw [le_sub_iff_add_le']
  rw [← le_sub_iff_add_le]
  refine ciSup_le fun ξT => ?_
  rw [le_sub_iff_add_le']
  have := key Γ S T hST ξS ξT
  linarith

theorem empty : Γ.restrictedCharFun ∅ = 0 := by
  have h : ∀ ξ η, Γ.bilin (Finset.map Fin.castSuccEmb ∅) ξ η = 0 := by
    intro ξ η
    simp [bilin, coalPayoff]
  have := ne_simplex Γ (RP ∅)
  have := ne_simplex Γ (RP ∅)ᶜ
  simp only [restrictedCharFun, extCharFun, h, ciInf_const, ciSup_const]

end P57dc

open TheoryOfGames.GeneralGames in
theorem solution {n : ℕ} (Γ : GeneralGame n) :
    IsRestrictedCharFunction Γ.restrictedCharFun ∧
      ∀ S : Finset (Fin n),
        Γ.restrictedCharFun Sᶜ ≤ Γ.restrictedCharFun Finset.univ - Γ.restrictedCharFun S := by
  refine ⟨⟨P57dc.empty Γ, fun S T h => P57dc.superadd Γ S T h⟩, fun S => ?_⟩
  have := P57dc.superadd Γ S Sᶜ disjoint_compl_right
  rw [Finset.union_compl] at this
  linarith
