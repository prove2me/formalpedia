-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.rowSignatureSectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:30:22.599217+00:00
-- url     : https://prove2.me/submissions/aeba51c9-44b8-4750-b8b2-3a787436280a

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

lemma X7RS_sig {n eta : ℕ} (K : Submodule F2 (Fin n → F2)) (W : Module.Basis (Fin eta) F2 K)
    (v w : Fin n) :
    (∀ x ∈ K, x v = x w) ↔ (fun a => (W a).1 v) = (fun a => (W a).1 w) := by
  constructor
  · intro h; funext a; exact h _ (W a).2
  · intro h x hx
    have hs := W.sum_repr ⟨x, hx⟩
    have hx' : x = ∑ a, (W.repr ⟨x, hx⟩ a) • (W a).1 := by
      have := congrArg Subtype.val hs
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hx']
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [congrFun h a]

end

end QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

open QAlgorithms.Papers.Independent.Information100.P22

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

theorem solution (m k eta : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (B : Matrix (Fin (m*k)) (Fin (m*k)) F2)
    (W : Module.Basis (Fin eta) F2 (LinearMap.ker B.transpose.mulVecLin)) :
    HasConstantSectors (LinearMap.ker B.transpose.mulVecLin) ↔
      ∀ signature : Fin eta → F2,
        m ∣ (Finset.univ.filter fun v => (fun a => (W a).1 v) = signature).card := by
  let sig : Fin (m*k) → (Fin eta → F2) := fun v a => (W a).1 v
  constructor
  · rintro ⟨e, he⟩ σ
    have h0 : ∀ j a, sig (e (j,a)) = sig (e (j, ⟨0, hm⟩)) := by
      intro j a
      exact (X7RS_sig _ W _ _).1 (fun x hx => he x hx j a ⟨0, hm⟩)
    rw [Finset.card_filter]
    rw [← e.sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.dvd_sum
    intro j _
    have : ∀ a' : Fin m, (fun a => (W a).1 (e (j, a'))) =
        (fun a => (W a).1 (e (j, ⟨0, hm⟩))) := fun a' => h0 j a'
    simp only [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    split_ifs <;> simp
  · intro h
    have hm0 : 0 < m := hm
    let C : (Fin eta → F2) → Type := fun σ => {v // sig v = σ}
    have hC : ∀ σ, m ∣ Fintype.card (C σ) := by
      intro σ
      have := h σ
      rw [Fintype.card_subtype]
      convert this
    let n : (Fin eta → F2) → ℕ := fun σ => Fintype.card (C σ) / m
    have hn : ∀ σ, Fintype.card (C σ) = n σ * m := fun σ => (Nat.div_mul_cancel (hC σ)).symm
    have hsum : ∑ σ, n σ = k := by
      have h1 : Fintype.card (Σ σ, C σ) = m * k := by
        rw [Fintype.card_congr (Equiv.sigmaFiberEquiv sig)]; simp
      rw [Fintype.card_sigma] at h1
      simp_rw [hn] at h1
      rw [← Finset.sum_mul, mul_comm] at h1
      exact Nat.eq_of_mul_eq_mul_left hm0 h1
    let e1 : Fin k ≃ Σ σ, Fin (n σ) :=
      Fintype.equivOfCardEq (by rw [Fintype.card_sigma]; simp [hsum])
    let e2 : (Σ σ, Fin (n σ)) × Fin m ≃ Σ σ, (Fin (n σ) × Fin m) :=
      { toFun := fun p => ⟨p.1.1, (p.1.2, p.2)⟩
        invFun := fun q => (⟨q.1, q.2.1⟩, q.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let f : ∀ σ, Fin (n σ) × Fin m ≃ C σ := fun σ =>
      Fintype.equivOfCardEq (by rw [hn]; simp)
    let e3 : (Σ σ, (Fin (n σ) × Fin m)) ≃ Σ σ, C σ := Equiv.sigmaCongrRight f
    let e4 : (Σ σ, C σ) ≃ Fin (m*k) := Equiv.sigmaFiberEquiv sig
    let e : Fin k × Fin m ≃ Fin (m*k) :=
      ((e1.prodCongr (Equiv.refl _)).trans (e2.trans (e3.trans e4)))
    have key : ∀ j a, sig (e (j,a)) = (e1 j).1 := by
      intro j a
      exact (f (e1 j).1 ((e1 j).2, a)).2
    refine ⟨e, fun x hx j a b => ?_⟩
    exact (X7RS_sig _ W _ _).2 (by
      change sig (e (j,a)) = sig (e (j,b)); rw [key, key]) x hx

end
