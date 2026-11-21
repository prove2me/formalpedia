-- Prove2me | solution 1 for RobustObedientPersuasion.Saddle.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:56:36.764621+00:00
-- url     : https://prove2.me/submissions/55772768-9973-4b20-aa80-55da6f3522d1

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_Model
import Definitions.Def_RobustObedientPersuasion_Saddle_Supplement_Unrestricted
import Definitions.Def_RobustObedientPersuasion_Saddle_FarkasMinkowski
universe v

section
namespace RobustObedientPersuasion.Saddle.Supplement.Dev
open RobustObedientPersuasion.Saddle RobustObedientPersuasion.Saddle.Supplement

section
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

end

end RobustObedientPersuasion.Saddle.Supplement.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Dev

end RobustObedientPersuasion.Saddle.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Dev
open RobustObedientPersuasion.Saddle RobustObedientPersuasion.Saddle.Supplement RobustObedientPersuasion.Saddle.Supplement.Dev

section
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

lemma obedienceRegion_isCompact (u : Ω → A → ℝ) (a : A) : IsCompact (obedienceRegion u a) := by
  refine (isCompact_stdSimplex ℝ Ω).of_isClosed_subset ?_ (fun ν hν => hν.1)
  have h1 : IsClosed (stdSimplex ℝ Ω) := (isCompact_stdSimplex ℝ Ω).isClosed
  have h2 : IsClosed {ν : Ω → ℝ | ∀ a' : A, 0 ≤ ∑ ω, ν ω * (u ω a - u ω a')} := by
    have : {ν : Ω → ℝ | ∀ a' : A, 0 ≤ ∑ ω, ν ω * (u ω a - u ω a')} =
        ⋂ a', {ν : Ω → ℝ | 0 ≤ ∑ ω, ν ω * (u ω a - u ω a')} := by ext; simp
    rw [this]
    exact isClosed_iInter fun a' => isClosed_le continuous_const
      (continuous_finset_sum _ fun ω _ => (continuous_apply ω).mul continuous_const)
  have h3 := h1.inter h2
  exact h3

lemma identifiedSet_eq (u : Ω → A → ℝ) (α : A → ℝ) :
    identifiedSet u α = (fun ν : A → Ω → ℝ => fun ω => ∑ a ∈ supp α, α a * ν a ω) ''
      Set.pi Set.univ (fun a => {x : Ω → ℝ | (a ∈ supp α → x ∈ obedienceRegion u a) ∧
        (a ∉ supp α → x = 0)}) := by
  classical
  ext μ
  constructor
  · rintro ⟨ν, hν, hμ⟩
    refine ⟨fun a => if a ∈ supp α then ν a else 0, ?_, ?_⟩
    · intro a _
      by_cases h : a ∈ supp α
      · simp [h, hν a h]
      · simp [h]
    · funext ω
      rw [hμ]
      exact Finset.sum_congr rfl fun a ha => by simp [ha]
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨ν, fun a ha => (hν a (Set.mem_univ a)).1 ha, fun ω => rfl⟩

lemma ident_compact (u : Ω → A → ℝ) (α : A → ℝ) : IsCompact (identifiedSet u α) := by
  rw [identifiedSet_eq]
  refine (isCompact_univ_pi fun a => ?_).image ?_
  · by_cases h : a ∈ supp α
    · have : {x : Ω → ℝ | (a ∈ supp α → x ∈ obedienceRegion u a) ∧ (a ∉ supp α → x = 0)} =
          obedienceRegion u a := by ext x; simp [h]
      rw [this]; exact obedienceRegion_isCompact u a
    · have : {x : Ω → ℝ | (a ∈ supp α → x ∈ obedienceRegion u a) ∧ (a ∉ supp α → x = 0)} =
          {0} := by ext x; simp [h]
      rw [this]; exact isCompact_singleton
  · exact continuous_pi fun ω => continuous_finset_sum _ fun a _ =>
      continuous_const.mul ((continuous_apply ω).comp (continuous_apply a))

lemma ident_nonempty {u : Ω → A → ℝ} {α : A → ℝ} (hdom : NoSupportedActionDominated u α) :
    (identifiedSet u α).Nonempty := by
  choose! ν hν using fun a (ha : a ∈ supp α) => hdom a ha
  exact ⟨_, ν, hν, fun ω => rfl⟩

end

end RobustObedientPersuasion.Saddle.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Dev

section FM
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Poly (S : Set (ι → ℝ)) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (a : κ → ι → ℝ) (b : κ → ℝ),
    S = {x | ∀ k, ∑ i, a k i * x i ≤ b k}

lemma Poly.isClosed {S : Set (ι → ℝ)} (h : Poly S) : IsClosed S := by
  obtain ⟨κ, _, a, b, rfl⟩ := h
  have : {x : ι → ℝ | ∀ k, ∑ i, a k i * x i ≤ b k} = ⋂ k, {x | ∑ i, a k i * x i ≤ b k} := by
    ext; simp
  rw [this]
  exact isClosed_iInter fun k => isClosed_le
    (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)) continuous_const

lemma sum_update (w x : ι → ℝ) (j : ι) (t : ℝ) :
    ∑ i, w i * Function.update x j t i = ∑ i, w i * x i + w j * (t - x j) := by
  have : ∀ i, w i * Function.update x j t i =
      w i * x i + (if i = j then w j * (t - x j) else 0) := by
    intro i
    by_cases h : i = j
    · subst h; simp only [Function.update_self, if_true]; ring
    · rw [Function.update_of_ne h, if_neg h, add_zero]
  simp_rw [this]
  rw [Finset.sum_add_distrib]
  simp

lemma fm_exists_t {κ : Type*} (Ps Ns : Finset κ) (β : κ → ℝ)
    (h : ∀ p ∈ Ps, ∀ q ∈ Ns, β q ≤ β p) :
    ∃ t, (∀ p ∈ Ps, t ≤ β p) ∧ ∀ q ∈ Ns, β q ≤ t := by
  by_cases hN : Ns.Nonempty
  · refine ⟨Ns.sup' hN β, fun p hp => Finset.sup'_le hN β fun q hq => h p hp q hq,
      fun q hq => Finset.le_sup' β hq⟩
  · by_cases hP : Ps.Nonempty
    · refine ⟨Ps.inf' hP β, fun p hp => Finset.inf'_le β hp, fun q hq => absurd ⟨q, hq⟩ hN⟩
    · exact ⟨0, fun p hp => absurd ⟨p, hp⟩ hP, fun q hq => absurd ⟨q, hq⟩ hN⟩

theorem poly_elim {S : Set (ι → ℝ)} (hS : Poly S) (j : ι) :
    Poly {x | ∃ t, Function.update x j t ∈ S} := by
  classical
  obtain ⟨κ, hκ, a, b, rfl⟩ := hS
  refine ⟨κ ⊕ (κ × κ), inferInstance,
    Sum.elim (fun k => if a k j = 0 then a k else 0)
      (fun pq => if (0 < a pq.1 j ∧ a pq.2 j < 0)
        then (fun i => a pq.1 j * a pq.2 i - a pq.2 j * a pq.1 i) else 0),
    Sum.elim (fun k => if a k j = 0 then b k else 0)
      (fun pq => if (0 < a pq.1 j ∧ a pq.2 j < 0)
        then a pq.1 j * b pq.2 - a pq.2 j * b pq.1 else 0), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  have hcomb : ∀ p q : κ, ∑ i, (a p j * a q i - a q j * a p i) * x i =
      a p j * ∑ i, a q i * x i - a q j * ∑ i, a p i * x i := by
    intro p q
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  constructor
  · rintro ⟨t, ht⟩ k'
    rcases k' with k | ⟨p, q⟩
    · by_cases h : a k j = 0
      · simp only [Sum.elim_inl, h, if_true]
        have := ht k
        rw [sum_update, h] at this
        simpa using this
      · simp [h]
    · by_cases h : 0 < a p j ∧ a q j < 0
      · simp only [Sum.elim_inr, h, and_self, if_true]
        have hp := ht p
        have hq := ht q
        rw [sum_update] at hp hq
        rw [hcomb]
        nlinarith [mul_le_mul_of_nonneg_left hq h.1.le,
          mul_le_mul_of_nonneg_left hp (neg_nonneg.2 h.2.le)]
      · simp [h]
  · intro h
    set β : κ → ℝ := fun k => (b k - ∑ i, a k i * x i + a k j * x j) / a k j with hβ
    have hPN : ∀ p ∈ Finset.univ.filter (fun k => 0 < a k j),
        ∀ q ∈ Finset.univ.filter (fun k => a k j < 0), β q ≤ β p := by
      intro p hp q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      have hh := h (Sum.inr (p, q))
      simp only [Sum.elim_inr, hp, hq, and_self, if_true] at hh
      rw [hcomb] at hh
      simp only [hβ]
      have hpq : a q j * a p j < 0 := mul_neg_of_neg_of_pos hq hp
      have hq0 : a q j ≠ 0 := hq.ne
      have hp0 : a p j ≠ 0 := hp.ne'
      have e : (b q - ∑ i, a q i * x i + a q j * x j) / a q j -
          (b p - ∑ i, a p i * x i + a p j * x j) / a p j =
          (a p j * (b q - ∑ i, a q i * x i + a q j * x j) -
            a q j * (b p - ∑ i, a p i * x i + a p j * x j)) / (a q j * a p j) := by
        field_simp
      have : (a p j * (b q - ∑ i, a q i * x i + a q j * x j) -
            a q j * (b p - ∑ i, a p i * x i + a p j * x j)) / (a q j * a p j) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by nlinarith) hpq.le
      linarith
    obtain ⟨t, ht1, ht2⟩ := fm_exists_t _ _ β hPN
    refine ⟨t, fun k => ?_⟩
    rw [sum_update]
    rcases lt_trichotomy (a k j) 0 with hneg | hz | hpos
    · have := ht2 k (by simp [hneg])
      have h2 := (div_le_iff_of_neg hneg).mp this
      nlinarith
    · have hk := h (Sum.inl k)
      simp only [Sum.elim_inl, hz, if_true] at hk
      rw [hz]; simpa using hk
    · have := ht1 k (by simp [hpos])
      have h2 := (le_div_iff₀ hpos).mp this
      nlinarith

end FM

end RobustObedientPersuasion.Saddle.Dev

namespace RobustObedientPersuasion.Saddle.Dev
section Comb
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma Poly_congr {S T : Set (ι → ℝ)} (h : S = T) (hT : Poly T) : Poly S := h ▸ hT

lemma Poly_le (φ : (ι → ℝ) →ₗ[ℝ] ℝ) (d : ℝ) : Poly {x | φ x ≤ d} := by
  refine ⟨Unit, inferInstance, fun _ i => φ (fun j => if i = j then 1 else 0), fun _ => d, ?_⟩
  ext x
  have hφ : φ x = ∑ i, φ (fun j => if i = j then 1 else 0) * x i := by
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  simp [hφ]

lemma Poly_inter {S T : Set (ι → ℝ)} (hS : Poly S) (hT : Poly T) : Poly (S ∩ T) := by
  obtain ⟨κ₁, _, a₁, b₁, rfl⟩ := hS
  obtain ⟨κ₂, _, a₂, b₂, rfl⟩ := hT
  refine ⟨κ₁ ⊕ κ₂, inferInstance, Sum.elim a₁ a₂, Sum.elim b₁ b₂, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr]

lemma Poly_of_fintype {κ : Type*} [Fintype κ] (a : κ → ι → ℝ) (b : κ → ℝ) :
    Poly {x | ∀ k, ∑ i, a k i * x i ≤ b k} := by
  let e := Fintype.equivFin κ
  refine ⟨Fin (Fintype.card κ), inferInstance, fun m => a (e.symm m), fun m => b (e.symm m), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h m
    exact h _
  · intro h k
    simpa using h (e k)

lemma Poly_iInter {κ : Type*} [Fintype κ] {S : κ → Set (ι → ℝ)} (h : ∀ k, Poly (S k)) :
    Poly (⋂ k, S k) := by
  choose κs hκs a b hS using h
  letI := hκs
  refine Poly_congr ?_ (Poly_of_fintype (κ := Σ k, κs k) (fun p => a p.1 p.2) (fun p => b p.1 p.2))
  ext x
  have : ∀ k, x ∈ S k ↔ ∀ j, ∑ i, a k j i * x i ≤ b k j := fun k => by rw [hS k]; rfl
  simp only [Set.mem_iInter, this, Sigma.forall, Set.mem_setOf_eq]

lemma Poly_ge (φ : (ι → ℝ) →ₗ[ℝ] ℝ) (d : ℝ) : Poly {x | d ≤ φ x} := by
  have := Poly_le (-φ) (-d)
  convert this using 2
  ext x
  simp [neg_le_neg_iff]

lemma Poly_eq (φ : (ι → ℝ) →ₗ[ℝ] ℝ) (d : ℝ) : Poly {x | φ x = d} := by
  have := Poly_inter (Poly_le φ d) (Poly_ge φ d)
  convert this using 1
  ext x
  simp [le_antisymm_iff]

def elimSet (J : Finset ι) (S : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {x | ∃ y, (∀ i ∉ J, y i = x i) ∧ y ∈ S}

theorem poly_elimSet (J : Finset ι) {S : Set (ι → ℝ)} (hS : Poly S) : Poly (elimSet J S) := by
  induction J using Finset.induction_on with
  | empty =>
    refine Poly_congr ?_ hS
    ext x
    simp only [elimSet, Finset.notMem_empty, not_false_eq_true, forall_const, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, hyS⟩
      have : y = x := funext hy
      exact this ▸ hyS
    · intro hx
      exact ⟨x, fun _ => rfl, hx⟩
  | insert j J hj ih =>
    refine Poly_congr ?_ (poly_elim ih j)
    ext x
    simp only [elimSet, Set.mem_setOf_eq, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨y, hy, hyS⟩
      refine ⟨y j, y, fun i hi => ?_, hyS⟩
      by_cases h : i = j
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hy i ⟨h, hi⟩
    · rintro ⟨t, y, hy, hyS⟩
      refine ⟨y, fun i hi => ?_, hyS⟩
      rw [hy i hi.2, Function.update_of_ne hi.1]

end Comb
end RobustObedientPersuasion.Saddle.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Dev
open RobustObedientPersuasion.Saddle RobustObedientPersuasion.Saddle.Supplement

section
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

lemma poly_embed {ι' κ' : Type*} [Fintype ι'] [Fintype κ'] [DecidableEq ι'] [DecidableEq κ']
    {E : Set (ι' ⊕ κ' → ℝ)} (h : Poly E) :
    Poly {μ : ι' → ℝ | (Sum.elim μ (fun _ => (0 : ℝ))) ∈ E} := by
  obtain ⟨κ, hκ, a, b, rfl⟩ := h
  refine ⟨κ, hκ, fun k i => a k (Sum.inl i), b, ?_⟩
  ext μ
  simp [Fintype.sum_sum_type]

def pr {ι : Type*} (i : ι) : (ι → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i

lemma pr_apply {ι : Type*} (i : ι) (x : ι → ℝ) : pr i x = x i := rfl

noncomputable def S1 (u : Ω → A → ℝ) (α : A → ℝ) : Set (Ω ⊕ (A × Ω) → ℝ) :=
  (⋂ ω, {x | (pr (Sum.inl ω) - ∑ a ∈ supp α, α a • pr (Sum.inr (a, ω)) : (Ω ⊕ (A × Ω) → ℝ) →ₗ[ℝ] ℝ) x = 0}) ∩
  ⋂ a : ↥(supp α), (((⋂ ω, {x | 0 ≤ (pr (Sum.inr (a.1, ω)) : (Ω ⊕ (A × Ω) → ℝ) →ₗ[ℝ] ℝ) x}) ∩
    {x | (∑ ω, pr (Sum.inr (a.1, ω)) : (Ω ⊕ (A × Ω) → ℝ) →ₗ[ℝ] ℝ) x = 1}) ∩
    ⋂ a', {x | 0 ≤ (∑ ω, (u ω a.1 - u ω a') • pr (Sum.inr (a.1, ω)) : (Ω ⊕ (A × Ω) → ℝ) →ₗ[ℝ] ℝ) x})

lemma poly_S1 [DecidableEq Ω] [DecidableEq A] (u : Ω → A → ℝ) (α : A → ℝ) : Poly (S1 u α) :=
  Poly_inter (Poly_iInter fun ω => Poly_eq _ 0)
    (Poly_iInter fun a => Poly_inter
      (Poly_inter (Poly_iInter fun ω => Poly_ge _ 0) (Poly_eq _ 1))
      (Poly_iInter fun a' => Poly_ge _ 0))

lemma mem_elim_S1 [DecidableEq Ω] [DecidableEq A] (u : Ω → A → ℝ) (α : A → ℝ)
    (x : Ω ⊕ (A × Ω) → ℝ) :
    x ∈ elimSet (Finset.univ.image Sum.inr) (S1 u α) ↔
      (fun ω => x (Sum.inl ω)) ∈ identifiedSet u α := by
  constructor
  · rintro ⟨y, hy, h1, h2⟩
    have hμ : ∀ ω, x (Sum.inl ω) = y (Sum.inl ω) := fun ω => (hy _ (by simp)).symm
    refine ⟨fun a ω => y (Sum.inr (a, ω)), fun a ha => ?_, fun ω => ?_⟩
    · have := Set.mem_iInter.mp h2 ⟨a, ha⟩
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, pr_apply,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
      refine ⟨⟨fun ω => this.1.1 ω, this.1.2⟩, fun a' => ?_⟩
      have h3 := this.2 a'
      simpa only [mul_comm] using h3
    · have := Set.mem_iInter.mp h1 ω
      simp only [Set.mem_setOf_eq, LinearMap.sub_apply, pr_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul] at this
      show x (Sum.inl ω) = ∑ a ∈ supp α, α a * y (Sum.inr (a, ω))
      rw [hμ ω]
      exact sub_eq_zero.mp this
  · rintro ⟨ν, hν, hμ⟩
    refine ⟨Sum.elim (fun ω => x (Sum.inl ω)) (fun p => ν p.1 p.2), ?_, ?_, ?_⟩
    · intro i hi
      rcases i with ω | p
      · rfl
      · exact absurd (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩) hi
    · refine Set.mem_iInter.mpr fun ω => ?_
      simp only [Set.mem_setOf_eq, LinearMap.sub_apply, pr_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr]
      exact sub_eq_zero.mpr (hμ ω)
    · refine Set.mem_iInter.mpr fun a => ?_
      have hn := hν a.1 a.2
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, pr_apply,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Sum.elim_inr]
      refine ⟨⟨fun ω => hn.1.1 ω, hn.1.2⟩, fun a' => ?_⟩
      have h3 := hn.2 a'
      simpa only [mul_comm] using h3

theorem poly_ident (u : Ω → A → ℝ) (α : A → ℝ) : ∃ (κ : Type) (_ : Fintype κ) (a : κ → Ω → ℝ)
    (b : κ → ℝ), identifiedSet u α = {x | ∀ k, ∑ ω, a k ω * x ω ≤ b k} := by
  classical
  have h := poly_elimSet (Finset.univ.image Sum.inr) (poly_S1 u α)
  have h2 := poly_embed h
  obtain ⟨κ, hκ, a, b, hab⟩ := h2
  refine ⟨κ, hκ, a, b, ?_⟩
  rw [← hab]
  ext μ
  rw [Set.mem_setOf_eq, mem_elim_S1]
  rfl

end

end RobustObedientPersuasion.Saddle.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Dev
open RobustObedientPersuasion.Saddle RobustObedientPersuasion.Saddle.Supplement

section
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

noncomputable def S2 {n : ℕ} (a : Fin n → Ω → ℝ) (b : Fin n → ℝ) :
    Set ((Ω ⊕ Unit) ⊕ (Fin n ⊕ Unit) → ℝ) :=
  (⋂ ω, {x | (pr (Sum.inl (Sum.inl ω)) - ∑ i, a i ω • pr (Sum.inr (Sum.inl i)) :
      ((Ω ⊕ Unit) ⊕ (Fin n ⊕ Unit) → ℝ) →ₗ[ℝ] ℝ) x = 0}) ∩
  ((({x | (pr (Sum.inl (Sum.inr ())) - ∑ i, b i • pr (Sum.inr (Sum.inl i)) -
      pr (Sum.inr (Sum.inr ())) : ((Ω ⊕ Unit) ⊕ (Fin n ⊕ Unit) → ℝ) →ₗ[ℝ] ℝ) x = 0}) ∩
    (⋂ i, {x | 0 ≤ (pr (Sum.inr (Sum.inl i)) :
      ((Ω ⊕ Unit) ⊕ (Fin n ⊕ Unit) → ℝ) →ₗ[ℝ] ℝ) x})) ∩
    {x | 0 ≤ (pr (Sum.inr (Sum.inr ())) : ((Ω ⊕ Unit) ⊕ (Fin n ⊕ Unit) → ℝ) →ₗ[ℝ] ℝ) x})

lemma poly_S2 [DecidableEq Ω] {n : ℕ} (a : Fin n → Ω → ℝ) (b : Fin n → ℝ) : Poly (S2 a b) :=
  Poly_inter (Poly_iInter fun ω => Poly_eq _ 0)
    (Poly_inter (Poly_inter (Poly_eq _ 0) (Poly_iInter fun i => Poly_ge _ 0)) (Poly_ge _ 0))

lemma mem_elim_S2 [DecidableEq Ω] {n : ℕ} (a : Fin n → Ω → ℝ) (b : Fin n → ℝ)
    (x : (Ω ⊕ Unit) ⊕ (Fin n ⊕ Unit) → ℝ) :
    x ∈ elimSet (Finset.univ.image Sum.inr) (S2 a b) ↔
      ((fun ω => x (Sum.inl (Sum.inl ω))), x (Sum.inl (Sum.inr ()))) ∈ characteristicCone a b := by
  constructor
  · rintro ⟨y, hy, h1, ⟨h2, h3⟩, h4⟩
    have hμ : ∀ s, x (Sum.inl s) = y (Sum.inl s) := fun s => (hy _ (by simp)).symm
    have e1 : ∀ ω, y (Sum.inl (Sum.inl ω)) = ∑ i, a i ω * y (Sum.inr (Sum.inl i)) := by
      intro ω
      have := Set.mem_iInter.mp h1 ω
      simp only [Set.mem_setOf_eq, LinearMap.sub_apply, pr_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul] at this
      exact sub_eq_zero.mp this
    have e2 := h2
    simp only [Set.mem_setOf_eq, LinearMap.sub_apply, pr_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul] at e2
    refine ⟨fun i => y (Sum.inr (Sum.inl i)), fun i => ?_, y (Sum.inr (Sum.inr ())), ?_, ?_⟩
    · have := Set.mem_iInter.mp h3 i
      simpa only [Set.mem_setOf_eq, pr_apply] using this
    · simpa only [Set.mem_setOf_eq, pr_apply] using h4
    · refine Prod.ext (funext fun ω => ?_) ?_
      · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [hμ, e1 ω]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · simp only
        rw [hμ]
        have : y (Sum.inl (Sum.inr ())) = ∑ i, b i * y (Sum.inr (Sum.inl i)) +
            y (Sum.inr (Sum.inr ())) := by linarith
        rw [this]
        congr 1
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rintro ⟨lam, hl, t, ht, hp⟩
    have hp1 := congrArg Prod.fst hp
    have hp2 := congrArg Prod.snd hp
    refine ⟨Sum.elim (fun s => x (Sum.inl s)) (Sum.elim lam (fun _ => t)), ?_, ?_⟩
    · intro i hi
      rcases i with s | q
      · rfl
      · exact absurd (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩) hi
    · refine ⟨Set.mem_iInter.mpr fun ω => ?_, ⟨⟨?_, Set.mem_iInter.mpr fun i => ?_⟩, ?_⟩⟩
      · simp only [Set.mem_setOf_eq, LinearMap.sub_apply, pr_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr]
        have := congrFun hp1 ω
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [this]
        refine sub_eq_zero.mpr (Finset.sum_congr rfl fun i _ => mul_comm _ _)
      · simp only [Set.mem_setOf_eq, LinearMap.sub_apply, pr_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr]
        simp only at hp2
        rw [hp2]
        have : ∑ i, b i * lam i = ∑ i, lam i * b i :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
        rw [this]; ring
      · simpa only [Set.mem_setOf_eq, pr_apply, Sum.elim_inl, Sum.elim_inr] using hl i
      · simpa only [Set.mem_setOf_eq, pr_apply, Sum.elim_inr] using ht

lemma cone_closed {n : ℕ} (a : Fin n → Ω → ℝ) (b : Fin n → ℝ) :
    IsClosed (characteristicCone a b) := by
  classical
  have h := poly_embed (poly_elimSet (Finset.univ.image Sum.inr) (poly_S2 a b))
  have hc := h.isClosed
  have hcont : Continuous (fun p : (Ω → ℝ) × ℝ =>
      (Sum.elim (fun ω => p.1 ω) (fun _ => p.2) : Ω ⊕ Unit → ℝ)) := by
    refine continuous_pi fun i => ?_
    rcases i with ω | u
    · exact (continuous_apply ω).comp continuous_fst
    · exact continuous_snd
  have := hc.preimage hcont
  convert this using 1
  ext p
  rw [Set.mem_preimage, Set.mem_setOf_eq, mem_elim_S2]
  rfl

end

end RobustObedientPersuasion.Saddle.Dev

namespace RobustObedientPersuasion.Saddle
open RobustObedientPersuasion.Saddle.Dev

theorem chk_lemma_2_1 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (u : Ω → A → ℝ) (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A)
    (hdom : NoSupportedActionDominated u α) :
    (identifiedSet u α).Nonempty ∧ IsCompact (identifiedSet u α) ∧
      ∃ (n : ℕ) (a : Fin n → Ω → ℝ) (b : Fin n → ℝ),
        identifiedSet u α = systemSet a b ∧ HasFarkasMinkowski a b := by
  refine ⟨ident_nonempty hdom, ident_compact u α, ?_⟩
  obtain ⟨κ, hκ, a, b, hP⟩ := poly_ident u α
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun i => a (e.symm i), fun i => b (e.symm i), ?_, cone_closed _ _⟩
  rw [hP]
  ext x
  simp only [systemSet, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact h _
  · intro h k
    simpa using h (e k)

end RobustObedientPersuasion.Saddle
end

theorem solution : type_of% @RobustObedientPersuasion.Saddle.chk_lemma_2_1 := @RobustObedientPersuasion.Saddle.chk_lemma_2_1
