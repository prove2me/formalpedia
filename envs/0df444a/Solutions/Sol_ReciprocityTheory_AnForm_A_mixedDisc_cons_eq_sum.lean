-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mixedDisc_cons_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:31.7348+00:00
-- url     : https://prove2.me/submissions/9cbad2e2-ef9e-4291-a261-206ef7b3161d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
section DzCalc
variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
end DzCalc
private lemma sum_superset_neg_one_pow_fin_eq_ite_univ (N : ℕ) (T : Finset (Fin N)) :
    ∑ S : Finset (Fin N), (if T ⊆ S then (-1 : ℂ) ^ (N - S.card) else 0) =
      if T = Finset.univ then 1 else 0 := by
  rw [← (Equiv.mk (compl : Finset (Fin N) → Finset (Fin N)) compl compl_compl
    compl_compl).sum_comp]
  simp only [Equiv.coe_fn_mk]
  have hc : ∀ S : Finset (Fin N), N - Sᶜ.card = S.card := by
    intro S
    have h1 := Finset.card_le_univ S
    rw [Fintype.card_fin] at h1
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hsub : ∀ S : Finset (Fin N), (T ⊆ Sᶜ) ↔ (S ⊆ Tᶜ) := fun S => by
    constructor
    · intro h x hx
      rw [Finset.mem_compl]
      intro hxT
      exact (Finset.mem_compl.mp (h hxT)) hx
    · intro h x hx
      rw [Finset.mem_compl]
      intro hxS
      exact (Finset.mem_compl.mp (h hxS)) hx
  simp only [hc, hsub]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun S : Finset (Fin N) => S ⊆ Tᶜ) = Tᶜ.powerset := by
    ext S; simp
  rw [hf]
  have h0 : (∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card) = if Tᶜ = ∅ then 1 else 0 :=
    Finset.sum_powerset_neg_one_pow_card
  have h1 : (∑ m ∈ Tᶜ.powerset, (-1 : ℂ) ^ m.card) =
      ((∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card : ℤ) : ℂ) := by simp
  rw [h1, h0]
  by_cases hT : T = Finset.univ
  · have h2 : Tᶜ = ∅ := by rw [hT]; simp
    simp [h2, hT]
  · have h2 : Tᶜ ≠ ∅ := by
      intro h
      apply hT
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hx' : x ∈ Tᶜ := Finset.mem_compl.mpr hx
      rw [h] at hx'
      simp at hx'
    simp [h2, hT]
private lemma mdisc_eq_inv_factorial_mul_sum_sign_prod {N : ℕ} (M : Fin N → Matrix (Fin N) (Fin N) ℂ) :
    mdisc M = (1 / (N.factorial : ℂ)) * ∑ σ : Equiv.Perm (Fin N), ∑ f : Fin N → Fin N,
      (if Finset.univ.image f = Finset.univ then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) := by
  unfold mdisc
  congr 1
  have hdet : ∀ S : Finset (Fin N), (∑ k ∈ S, M k).det =
      ∑ σ : Equiv.Perm (Fin N), ∑ f : Fin N → Fin N,
        (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) := by
    intro S
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hpf : Fintype.piFinset (fun _ : Fin N => S) =
        Finset.univ.filter (fun f : Fin N → Fin N => ∀ i, f i ∈ S) := by
      ext f; simp [Fintype.mem_piFinset]
    have hp : ∏ i, (∑ k ∈ S, M k) (σ i) i =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin N => S), ∏ i, M (f i) (σ i) i := by
      simp only [Matrix.sum_apply]
      rw [Finset.prod_univ_sum]
    rw [hp, hpf, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [mul_ite, mul_zero]
  simp only [hdet, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hiff : ∀ S : Finset (Fin N), (∀ i, f i ∈ S) ↔ Finset.univ.image f ⊆ S := fun S => by
    simp [Finset.image_subset_iff]
  have hS : ∀ S : Finset (Fin N), (-1 : ℂ) ^ (N - S.card) *
      (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) =
      (if Finset.univ.image f ⊆ S then (-1 : ℂ) ^ (N - S.card) else 0) *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i) := by
    intro S
    by_cases h : ∀ i, f i ∈ S
    · rw [if_pos h, if_pos ((hiff S).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hiff S).mpr h')), mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun S _ => hS S, ← Finset.sum_mul, sum_superset_neg_one_pow_fin_eq_ite_univ]
  split_ifs <;> simp
private lemma prod_cons_eq_sum_mul_prod_cons_single {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (f : Fin (n + 1) → Fin (n + 1)) (hf : Finset.univ.image f = Finset.univ) :
    ∏ i, (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
      ∑ j, ∑ k, A j k * ∏ i, (Fin.cons (Matrix.single j k 1) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
  have hs : Function.Surjective f := fun y => by
    have hy : y ∈ Finset.univ.image f := by rw [hf]; exact Finset.mem_univ y
    simpa using hy
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr hs
  obtain ⟨i0, hi0⟩ := hs 0
  have hne : ∀ i ∈ Finset.univ.erase i0, f i ≠ 0 := fun i hi' h =>
    (Finset.mem_erase.mp hi').1 (hi (h.trans hi0.symm))
  have hrest : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∏ i ∈ Finset.univ.erase i0,
        (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
      ∏ i ∈ Finset.univ.erase i0,
        (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
    intro X
    refine Finset.prod_congr rfl fun i hi' => ?_
    obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr (hne i hi')
    rw [← hm, Fin.cons_succ, Fin.cons_succ]
  have hsplit : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∏ i, (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
        X (σ i0) i0 * ∏ i ∈ Finset.univ.erase i0,
          (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
    intro X
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), hrest X, hi0, Fin.cons_zero]
  simp only [hsplit]
  simp only [← mul_assoc, ← Finset.sum_mul]
  congr 1
  simp only [Matrix.single_apply]
  first
    | (rw [Finset.sum_eq_single (σ i0) (fun x _ hx => by simp [hx]) (by simp)]
       rw [Finset.sum_eq_single i0 (fun x _ hx => by simp [hx]) (by simp)]
       simp)
    | (simp [ite_and])
    | (simp [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq])
end
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k * mixedCof B j k := by
  have e1 : ∀ g : Fin (n + 1) → Fin (n + 1) → Equiv.Perm (Fin (n + 1)) →
      (Fin (n + 1) → Fin (n + 1)) → ℂ,
      ∑ j, ∑ k, ∑ σ, ∑ f, g j k σ f = ∑ σ, ∑ f, ∑ j, ∑ k, g j k σ f := by
    intro g
    calc ∑ j, ∑ k, ∑ σ, ∑ f, g j k σ f = ∑ j, ∑ σ, ∑ k, ∑ f, g j k σ f :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ σ, ∑ j, ∑ k, ∑ f, g j k σ f := Finset.sum_comm
      _ = ∑ σ, ∑ j, ∑ f, ∑ k, g j k σ f :=
          Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ σ, ∑ f, ∑ j, ∑ k, g j k σ f := Finset.sum_congr rfl fun σ _ => Finset.sum_comm
  have ht : ∀ (σ : Equiv.Perm (Fin (n + 1))) (f : Fin (n + 1) → Fin (n + 1)),
      (if Finset.univ.image f = Finset.univ then ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i
        else 0) =
      ∑ j, ∑ k, A j k * (if Finset.univ.image f = Finset.univ then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (Fin.cons (Matrix.single j k 1) B :
          Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i else 0) := by
    intro σ f
    by_cases hf : Finset.univ.image f = Finset.univ
    · simp only [if_pos hf]
      rw [prod_cons_eq_sum_mul_prod_cons_single A B σ f hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · simp [if_neg hf]
  rw [mdisc_eq_inv_factorial_mul_sum_sign_prod]
  simp only [mixedCof, mdisc_eq_inv_factorial_mul_sum_sign_prod]
  simp only [ht]
  simp only [Finset.mul_sum, e1]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun f _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.AnForm.A
