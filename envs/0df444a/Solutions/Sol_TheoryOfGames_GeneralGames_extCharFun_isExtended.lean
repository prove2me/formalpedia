-- Prove2me | solution 1 for TheoryOfGames.GeneralGames.extCharFun_isExtended
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:56:23.618563+00:00
-- url     : https://prove2.me/submissions/ab671449-1bca-47fb-9018-314244eb587b

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

set_option autoImplicit false

namespace P4ea2e32a

open Finset

section Generic

variable {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']

def Ex {X : Type*} [Fintype X] (p : X → ℝ) (h : X → ℝ) : ℝ := ∑ x, p x * h x

def K (F : A → B → ℝ) (ξ : A → ℝ) (η : B → ℝ) : ℝ := ∑ a, ∑ b, F a b * ξ a * η b

lemma K_eq_E (F : A → B → ℝ) (ξ : A → ℝ) (η : B → ℝ) :
    K F ξ η = Ex ξ (fun a => Ex η (fun b => F a b)) := by
  unfold K Ex; refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring

lemma E_add (p h1 h2 : A → ℝ) : Ex p (fun x => h1 x + h2 x) = Ex p h1 + Ex p h2 := by
  unfold Ex; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => by ring

lemma E_neg (p h : A → ℝ) : Ex p (fun x => - h x) = - Ex p h := by
  unfold Ex; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun x _ => by ring

lemma E_congr (p : A → ℝ) {h1 h2 : A → ℝ} (h : ∀ x, h1 x = h2 x) : Ex p h1 = Ex p h2 := by
  unfold Ex; exact Finset.sum_congr rfl fun x _ => by rw [h x]

lemma E_ge (p : stdSimplex ℝ A) (h : A → ℝ) (c : ℝ) (hc : ∀ x, c ≤ h x) :
    c ≤ Ex (p : A → ℝ) h := by
  unfold Ex
  calc c = ∑ x, p x * c := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hc x) (stdSimplex.zero_le p x)

lemma E_le (p : stdSimplex ℝ A) (h : A → ℝ) (c : ℝ) (hc : ∀ x, h x ≤ c) :
    Ex (p : A → ℝ) h ≤ c := by
  unfold Ex
  calc _ ≤ ∑ x, p x * c := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hc x) (stdSimplex.zero_le p x)
    _ = c := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

lemma abs_E_le (p : stdSimplex ℝ A) (h : A → ℝ) (c : ℝ) (hc : ∀ x, |h x| ≤ c) :
    |Ex (p : A → ℝ) h| ≤ c :=
  abs_le.2 ⟨E_ge p h (-c) (fun x => (abs_le.1 (hc x)).1),
    E_le p h c (fun x => (abs_le.1 (hc x)).2)⟩

lemma E_comm (p : A → ℝ) (q : B → ℝ) (h : A → B → ℝ) :
    Ex p (fun a => Ex q (fun b => h a b)) = Ex q (fun b => Ex p (fun a => h a b)) := by
  unfold Ex; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

lemma E_map (f : A → B) (p : stdSimplex ℝ A) (h : B → ℝ) :
    Ex (stdSimplex.map f p : B → ℝ) h = Ex (p : A → ℝ) (fun x => h (f x)) := by
  classical
  unfold Ex
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => p x * h (f x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

def prodS (p : stdSimplex ℝ A) (q : stdSimplex ℝ B) : stdSimplex ℝ (A × B) :=
  ⟨fun x => p x.1 * q x.2, fun x => mul_nonneg (stdSimplex.zero_le p _) (stdSimplex.zero_le q _),
    by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]⟩

lemma E_prod (p : stdSimplex ℝ A) (q : stdSimplex ℝ B) (h : A × B → ℝ) :
    Ex (prodS p q : A × B → ℝ) h = Ex (p : A → ℝ) (fun a => Ex (q : B → ℝ) (fun b => h (a, b))) := by
  unfold Ex prodS
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by show p a * q b * h (a, b) = _; ring

lemma K_bound (F : A → B → ℝ) (ξ : stdSimplex ℝ A) (η : stdSimplex ℝ B) :
    |K F ξ η| ≤ ∑ a, ∑ b, |F a b| := by
  rw [K_eq_E]
  apply abs_E_le; intro a; apply abs_E_le; intro b
  calc |F a b| ≤ ∑ b, |F a b| :=
        Finset.single_le_sum (f := fun b => |F a b|) (fun _ _ => abs_nonneg _) (mem_univ b)
    _ ≤ ∑ a, ∑ b, |F a b| :=
        Finset.single_le_sum (f := fun a => ∑ b, |F a b|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_univ a)

noncomputable def val (F : A → B → ℝ) : ℝ :=
  ⨆ ξ : stdSimplex ℝ A, ⨅ η : stdSimplex ℝ B, K F ξ η

lemma simplex_nonempty (X : Type*) [Fintype X] [Nonempty X] : Nonempty (stdSimplex ℝ X) := by
  classical
  exact ⟨⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary X)⟩⟩

lemma inf_le (F : A → B → ℝ) (ξ : stdSimplex ℝ A) (η : stdSimplex ℝ B) :
    ⨅ η' : stdSimplex ℝ B, K F ξ η' ≤ K F ξ η :=
  ciInf_le ⟨-(∑ a, ∑ b, |F a b|), by
    rintro _ ⟨η', rfl⟩; exact (abs_le.1 (K_bound F ξ η')).1⟩ η

lemma le_val [Nonempty B] (F : A → B → ℝ) (ξ : stdSimplex ℝ A) :
    ⨅ η : stdSimplex ℝ B, K F ξ η ≤ val F := by
  haveI := simplex_nonempty B
  unfold val
  refine le_ciSup (f := fun ξ : stdSimplex ℝ A => ⨅ η : stdSimplex ℝ B, K F ξ η) ⟨∑ a, ∑ b, |F a b|, ?_⟩ ξ
  rintro _ ⟨ξ', rfl⟩
  exact (inf_le F ξ' (Classical.arbitrary _)).trans (abs_le.1 (K_bound F _ _)).2

lemma saddle [Nonempty A] [Nonempty B] (F : A → B → ℝ) :
    ∃ ξs : stdSimplex ℝ A, ∃ ηs : stdSimplex ℝ B,
      ∀ ξ : stdSimplex ℝ A, ∀ η : stdSimplex ℝ B, K F ξ ηs ≤ K F ξs η := by
  classical
  have neA : (stdSimplex ℝ A).Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary A)⟩
  have neB : (stdSimplex ℝ B).Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary B)⟩
  have hcont1 : ∀ ξ : A → ℝ, Continuous fun η : B → ℝ => K F ξ η := by
    intro ξ; unfold K; fun_prop
  have hcont2 : ∀ η : B → ℝ, Continuous fun ξ : A → ℝ => K F ξ η := by
    intro η; unfold K; fun_prop
  have hlin1 : ∀ ξ : A → ℝ, ∀ x y : B → ℝ, ∀ a b : ℝ,
      K F ξ (a • x + b • y) = a • K F ξ x + b • K F ξ y := by
    intro ξ x y a b
    simp only [K, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hlin2 : ∀ η : B → ℝ, ∀ x y : A → ℝ, ∀ a b : ℝ,
      K F (a • x + b • y) η = a • K F x η + b • K F y η := by
    intro η x y a b
    simp only [K, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨a, ha, b, hb, h⟩ := Sion.exists_isSaddlePointOn (E := B → ℝ) (F := A → ℝ)
    (X := stdSimplex ℝ B) (Y := stdSimplex ℝ A) (f := fun η ξ => K F ξ η)
    neB (convex_stdSimplex ℝ B) (isCompact_stdSimplex ℝ B)
    (fun ξ _ => (hcont1 ξ).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun ξ _ => (ConvexOn.quasiconvexOn ⟨convex_stdSimplex ℝ B,
      fun x _ y _ a b _ _ _ => le_of_eq (hlin1 ξ x y a b)⟩))
    (convex_stdSimplex ℝ A) neA (isCompact_stdSimplex ℝ A)
    (fun η _ => (hcont2 η).upperSemicontinuous.upperSemicontinuousOn _)
    (fun η _ => (ConcaveOn.quasiconcaveOn ⟨convex_stdSimplex ℝ A,
      fun x _ y _ a b _ _ _ => le_of_eq (hlin2 η x y a b).symm⟩))
  exact ⟨⟨b, hb⟩, ⟨a, ha⟩, fun ξ η => h η η.2 ξ ξ.2⟩

lemma val_eq [Nonempty A] [Nonempty B] (F : A → B → ℝ) (ξs : stdSimplex ℝ A)
    (ηs : stdSimplex ℝ B) (hs : ∀ ξ : stdSimplex ℝ A, ∀ η : stdSimplex ℝ B,
      K F ξ ηs ≤ K F ξs η) : val F = K F ξs ηs := by
  haveI := simplex_nonempty A
  haveI := simplex_nonempty B
  apply le_antisymm
  · exact ciSup_le fun ξ => (inf_le F ξ ηs).trans (hs ξ ηs)
  · exact le_trans (le_ciInf fun η => hs ξs η) (le_val F ξs)

lemma map_left_inv {X Y : Type*} [Fintype X] [Fintype Y] (g : X → Y) (h : Y → X)
    (hgh : ∀ y, g (h y) = y) (p : stdSimplex ℝ Y) :
    stdSimplex.map g (stdSimplex.map h p) = p := by
  rw [stdSimplex.map_comp_apply]
  have : g.comp h = id := funext hgh
  rw [this, stdSimplex.map_id_apply]

lemma val_swap [Nonempty A] [Nonempty B] [Nonempty A'] [Nonempty B']
    (F : A → B → ℝ) (G : A' → B' → ℝ)
    (g1 : A' → B) (h1 : B → A') (hg1 : ∀ b, g1 (h1 b) = b)
    (g2 : B' → A) (h2 : A → B') (hg2 : ∀ a, g2 (h2 a) = a)
    (hG : ∀ a' b', G a' b' = - F (g2 b') (g1 a')) : val G = - val F := by
  obtain ⟨ξs, ηs, hs⟩ := saddle F
  rw [val_eq F ξs ηs hs]
  have key : ∀ (ξ' : stdSimplex ℝ A') (η' : stdSimplex ℝ B'),
      K G ξ' η' = - K F (stdSimplex.map g2 η') (stdSimplex.map g1 ξ') := by
    intro ξ' η'
    rw [K_eq_E, K_eq_E, E_map]
    simp only [E_map]
    rw [E_comm, ← E_neg]
    refine E_congr _ fun b' => ?_
    beta_reduce
    rw [← E_neg]
    exact E_congr _ fun a' => by beta_reduce; exact hG a' b'
  haveI := simplex_nonempty A'
  haveI := simplex_nonempty B'
  apply le_antisymm
  · refine ciSup_le fun ξ' => (inf_le G ξ' (stdSimplex.map h2 ξs)).trans ?_
    rw [key, map_left_inv g2 h2 hg2]
    exact neg_le_neg (hs ξs _)
  · refine le_trans (le_ciInf fun η' => ?_) (le_val G (stdSimplex.map h1 ηs))
    rw [key, map_left_inv g1 h1 hg1]
    exact neg_le_neg (hs _ ηs)

lemma val_le [Nonempty A] (F : A → B → ℝ) (c : ℝ)
    (h : ∀ ξ : stdSimplex ℝ A, ⨅ η : stdSimplex ℝ B, K F ξ η ≤ c) : val F ≤ c := by
  haveI := simplex_nonempty A
  unfold val
  exact ciSup_le h

end Generic

section Game

open TheoryOfGames.GeneralGames GeneralGame

variable {n : ℕ} (Γ : GeneralGame n)

lemma cs_nonempty (R : Finset (Fin n)) : Nonempty (Γ.CoalStrat R) :=
  ⟨fun k => ⟨0, Γ.β_pos k⟩⟩

lemma extCharFun_eq (S : Finset (Fin (n + 1))) : Γ.extCharFun S = val (Γ.coalPayoff S) := rfl

lemma mem_realPart (S : Finset (Fin (n + 1))) (k : Fin n) :
    k ∈ realPart S ↔ Fin.castSucc k ∈ S := by
  show k ∈ Finset.univ.filter (fun i : Fin n => Fin.castSucc i ∈ S) ↔ _
  simp

lemma sum_extH (τ : (k : Fin n) → Fin (Γ.β k)) : ∑ k, Γ.extH τ k = 0 := by
  rw [Fin.sum_univ_castSucc]; simp [GeneralGame.extH]

def tr {R R' : Finset (Fin n)} (h : ∀ k, k ∈ R' → k ∈ R) (a : Γ.CoalStrat R) :
    Γ.CoalStrat R' :=
  fun k => a ⟨k.1, h k.1 k.2⟩

lemma part_a : Γ.extCharFun ∅ = 0 := by
  haveI : ∀ R : Finset (Fin n), Nonempty (Γ.CoalStrat R) := fun R => cs_nonempty Γ R
  haveI := simplex_nonempty (Γ.CoalStrat (realPart (∅ : Finset (Fin (n + 1)))))
  haveI := simplex_nonempty (Γ.CoalStrat (realPart (∅ : Finset (Fin (n + 1))))ᶜ)
  unfold GeneralGame.extCharFun
  have : ∀ ξ η, Γ.bilin ∅ ξ η = 0 := by
    intro ξ η; simp [GeneralGame.bilin, GeneralGame.coalPayoff]
  simp only [this, ciInf_const, ciSup_const]

lemma part_b (S : Finset (Fin (n + 1))) : Γ.extCharFun Sᶜ = - Γ.extCharFun S := by
  haveI : ∀ R : Finset (Fin n), Nonempty (Γ.CoalStrat R) := fun R => cs_nonempty Γ R
  have hm : ∀ k, k ∈ realPart Sᶜ ↔ k ∉ realPart S := by
    intro k; simp [mem_realPart]
  have p1 : ∀ k, k ∈ (realPart S)ᶜ → k ∈ realPart Sᶜ := fun k hk =>
    (hm k).2 (Finset.mem_compl.1 hk)
  have q1 : ∀ k, k ∈ realPart Sᶜ → k ∈ (realPart S)ᶜ := fun k hk =>
    Finset.mem_compl.2 ((hm k).1 hk)
  have p2 : ∀ k, k ∈ realPart S → k ∈ (realPart Sᶜ)ᶜ := fun k hk =>
    Finset.mem_compl.2 (fun h => (hm k).1 h hk)
  have q2 : ∀ k, k ∈ (realPart Sᶜ)ᶜ → k ∈ realPart S := fun k hk => by
    by_contra h; exact Finset.mem_compl.1 hk ((hm k).2 h)
  rw [extCharFun_eq, extCharFun_eq]
  refine val_swap _ _ (tr Γ p1) (tr Γ q1) (fun _ => rfl) (tr Γ p2) (tr Γ q2) (fun _ => rfl) ?_
  intro a' b'
  have hj : Γ.joint (realPart Sᶜ) a' b' = Γ.joint (realPart S) (tr Γ p2 b') (tr Γ p1 a') := by
    funext k
    simp only [GeneralGame.joint, tr]
    by_cases h1 : k ∈ realPart Sᶜ
    · have h2 : k ∉ realPart S := (hm k).1 h1
      rw [dif_pos h1, dif_neg h2]
    · have h2 : k ∈ realPart S := by by_contra h2; exact h1 ((hm k).2 h2)
      rw [dif_neg h1, dif_pos h2]
  unfold GeneralGame.coalPayoff
  rw [hj]
  have := Finset.sum_compl_add_sum S (Γ.extH (Γ.joint (realPart S) (tr Γ p2 b') (tr Γ p1 a')))
  rw [sum_extH] at this
  linarith

variable {Γ}

def merge {S T : Finset (Fin (n + 1))} (a : Γ.CoalStrat (realPart S))
    (b : Γ.CoalStrat (realPart T)) : Γ.CoalStrat (realPart (S ∪ T)) :=
  fun k => if h : k.1 ∈ realPart S then a ⟨k.1, h⟩ else b ⟨k.1, by
    have := k.2
    simp only [mem_realPart, Finset.mem_union] at this h ⊢; tauto⟩

def rS {S T : Finset (Fin (n + 1))} (b : Γ.CoalStrat (realPart T))
    (σ : Γ.CoalStrat (realPart (S ∪ T))ᶜ) : Γ.CoalStrat (realPart S)ᶜ :=
  fun k => if h : k.1 ∈ realPart T then b ⟨k.1, h⟩ else σ ⟨k.1, by
    have := k.2
    simp only [Finset.mem_compl, mem_realPart, Finset.mem_union] at this h ⊢; tauto⟩

def rT {S T : Finset (Fin (n + 1))} (a : Γ.CoalStrat (realPart S))
    (σ : Γ.CoalStrat (realPart (S ∪ T))ᶜ) : Γ.CoalStrat (realPart T)ᶜ :=
  fun k => if h : k.1 ∈ realPart S then a ⟨k.1, h⟩ else σ ⟨k.1, by
    have := k.2
    simp only [Finset.mem_compl, mem_realPart, Finset.mem_union] at this h ⊢; tauto⟩

lemma joint_merge_S {S T : Finset (Fin (n + 1))} (a : Γ.CoalStrat (realPart S))
    (b : Γ.CoalStrat (realPart T)) (σ : Γ.CoalStrat (realPart (S ∪ T))ᶜ) :
    Γ.joint (realPart (S ∪ T)) (merge a b) σ = Γ.joint (realPart S) a (rS b σ) := by
  funext k
  by_cases hS : k ∈ realPart S
  · have hU : k ∈ realPart (S ∪ T) := by
      simp only [mem_realPart, Finset.mem_union] at hS ⊢; tauto
    simp [GeneralGame.joint, merge, hS, hU]
  · by_cases hT : k ∈ realPart T
    · have hU : k ∈ realPart (S ∪ T) := by
        simp only [mem_realPart, Finset.mem_union] at hT ⊢; tauto
      simp [GeneralGame.joint, merge, rS, hS, hT, hU]
    · have hU : k ∉ realPart (S ∪ T) := by
        simp only [mem_realPart, Finset.mem_union] at hS hT ⊢; tauto
      simp [GeneralGame.joint, merge, rS, hS, hT, hU]

lemma joint_merge_T {S T : Finset (Fin (n + 1))} (hST : Disjoint S T)
    (a : Γ.CoalStrat (realPart S))
    (b : Γ.CoalStrat (realPart T)) (σ : Γ.CoalStrat (realPart (S ∪ T))ᶜ) :
    Γ.joint (realPart (S ∪ T)) (merge a b) σ = Γ.joint (realPart T) b (rT a σ) := by
  funext k
  by_cases hS : k ∈ realPart S
  · have hU : k ∈ realPart (S ∪ T) := by
      simp only [mem_realPart, Finset.mem_union] at hS ⊢; tauto
    have hT : k ∉ realPart T := by
      rw [mem_realPart] at hS ⊢; exact Finset.disjoint_left.1 hST hS
    simp [GeneralGame.joint, merge, rT, hS, hT, hU]
  · by_cases hT : k ∈ realPart T
    · have hU : k ∈ realPart (S ∪ T) := by
        simp only [mem_realPart, Finset.mem_union] at hT ⊢; tauto
      simp [GeneralGame.joint, merge, rT, hS, hT, hU]
    · have hU : k ∉ realPart (S ∪ T) := by
        simp only [mem_realPart, Finset.mem_union] at hS hT ⊢; tauto
      simp [GeneralGame.joint, merge, rT, hS, hT, hU]

lemma payoff_split {S T : Finset (Fin (n + 1))} (hST : Disjoint S T)
    (a : Γ.CoalStrat (realPart S))
    (b : Γ.CoalStrat (realPart T)) (σ : Γ.CoalStrat (realPart (S ∪ T))ᶜ) :
    Γ.coalPayoff (S ∪ T) (merge a b) σ =
      Γ.coalPayoff S a (rS b σ) + Γ.coalPayoff T b (rT a σ) := by
  unfold GeneralGame.coalPayoff
  rw [Finset.sum_union hST]
  congr 1
  · rw [joint_merge_S]
  · rw [joint_merge_T hST]

variable (Γ)

lemma part_c (S T : Finset (Fin (n + 1))) (hST : Disjoint S T) :
    Γ.extCharFun S + Γ.extCharFun T ≤ Γ.extCharFun (S ∪ T) := by
  haveI : ∀ R : Finset (Fin n), Nonempty (Γ.CoalStrat R) := fun R => cs_nonempty Γ R
  rw [extCharFun_eq, extCharFun_eq, extCharFun_eq]
  have key : ∀ (ξS : stdSimplex ℝ (Γ.CoalStrat (realPart S)))
      (ξT : stdSimplex ℝ (Γ.CoalStrat (realPart T))),
      (⨅ η : stdSimplex ℝ (Γ.CoalStrat (realPart S)ᶜ), K (Γ.coalPayoff S) ξS η) +
      (⨅ η : stdSimplex ℝ (Γ.CoalStrat (realPart T)ᶜ), K (Γ.coalPayoff T) ξT η) ≤
        val (Γ.coalPayoff (S ∪ T)) := by
    intro ξS ξT
    refine le_trans ?_ (le_val _ (stdSimplex.map (fun p => merge p.1 p.2) (prodS ξS ξT)))
    haveI := simplex_nonempty (Γ.CoalStrat (realPart (S ∪ T))ᶜ)
    refine le_ciInf fun η => ?_
    have hK : K (Γ.coalPayoff (S ∪ T))
        (stdSimplex.map (fun p => merge p.1 p.2) (prodS ξS ξT) : _ → ℝ) η =
        K (Γ.coalPayoff S) ξS (stdSimplex.map (fun p => rS p.1 p.2) (prodS ξT η) : _ → ℝ) +
        K (Γ.coalPayoff T) ξT (stdSimplex.map (fun p => rT p.1 p.2) (prodS ξS η) : _ → ℝ) := by
      simp only [K_eq_E, E_map, E_prod]
      rw [E_comm (ξT : _ → ℝ) (ξS : _ → ℝ), ← E_add]
      refine E_congr _ fun a => ?_
      beta_reduce
      rw [← E_add]
      refine E_congr _ fun b => ?_
      beta_reduce
      rw [← E_add]
      exact E_congr _ fun σ => payoff_split hST a b σ
    rw [hK]
    exact add_le_add (inf_le _ _ _) (inf_le _ _ _)
  have h1 : ∀ ξS : stdSimplex ℝ (Γ.CoalStrat (realPart S)),
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat (realPart S)ᶜ), K (Γ.coalPayoff S) ξS η ≤
        val (Γ.coalPayoff (S ∪ T)) - val (Γ.coalPayoff T) := by
    intro ξS
    have : val (Γ.coalPayoff T) ≤ val (Γ.coalPayoff (S ∪ T)) -
        ⨅ η : stdSimplex ℝ (Γ.CoalStrat (realPart S)ᶜ), K (Γ.coalPayoff S) ξS η :=
      val_le _ _ fun ξT => by linarith [key ξS ξT]
    linarith
  have := val_le _ _ h1
  linarith

end Game

end P4ea2e32a

open TheoryOfGames.GeneralGames in
theorem solution {n : ℕ} (Γ : GeneralGame n) :
    IsExtendedCharFunction Γ.extCharFun := by
  exact ⟨P4ea2e32a.part_a Γ, P4ea2e32a.part_b Γ, P4ea2e32a.part_c Γ⟩
