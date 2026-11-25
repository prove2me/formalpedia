-- Prove2me | solution 1 for UpperTheory.discr_CMDatum_eq_prod_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:04:19.970162+00:00
-- url     : https://prove2.me/submissions/4f43781e-6f74-4a7f-b220-1887d3445a82

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_DiscrCMDatumEqProdPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
noncomputable section
namespace UpperTheory.PlacesDiscr
section Emb
variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
private theorem restrEmb_spec (hv : v.Integers O) (φ : E →ₐ[ℚ] C) (a : 𝓞 E) :
    algebraMap O C (restrEmb hv φ a) = φ (a : E) :=
  (exists_lift_val hv φ a).choose_spec
variable {p : ℕ} [Fact p.Prime]
end Emb
section Split
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [StarRing R]
variable {s : ℕ} (w : Fin s → Place p R)
variable {w}
end Split
end UpperTheory.PlacesDiscr
end
private theorem tauExt_comp_star_eq_tauExt_sig {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [StarRing R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (τ : R →+* O) (x : ℤ_[p] ⊗[ℤ] R) :
    tauExt (τ.comp (starRingEnd R)) x = tauExt τ (sig p R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [tauExt, sig, starRingEnd_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
private theorem eq_zero_or_one_of_idempotent_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (x : O) (hx : x * x = x) : x = 0 ∨ x = 1 := by
  have h := congrArg (algebraMap O C) hx
  rw [map_mul] at h
  have h2 : algebraMap O C x * (algebraMap O C x - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    exact hv.hom_inj (by rw [h3, map_zero])
  · right
    exact hv.hom_inj (by rw [map_one]; exact sub_eq_zero.mp h3)
private theorem det_linearForms_basis_change {A M O κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing O]
    [Algebra A O] [Fintype κ] [DecidableEq κ] (f : κ → (M →ₗ[A] O)) (γ γ' : Module.Basis κ A M) :
    (Matrix.of fun m k => f k (γ' m)).det
      = algebraMap A O (γ.toMatrix γ').det * (Matrix.of fun m k => f k (γ m)).det := by
  have key : (Matrix.of fun m k => f k (γ' m))
      = Matrix.transpose ((γ.toMatrix γ').map (algebraMap A O)) * Matrix.of fun m k => f k (γ m) := by
    ext m k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
    conv_lhs => rw [← γ.sum_toMatrix_smul_self γ' m]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Algebra.smul_def]
  rw [key, Matrix.det_mul, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
private theorem det_blockDiagonal'_eq_prod_det {s : ℕ} {m : Fin s → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {O : Type} [CommRing O] (d : ∀ i, Matrix (m i) (m i) O) :
    (Matrix.blockDiagonal' d).det = ∏ i, (d i).det := by
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  let e : m k ≃ {x : (Σ i, m i) // x.1 = k} :=
    { toFun := fun a => ⟨⟨k, a⟩, rfl⟩
      invFun := fun x => cast (congrArg m x.2) x.1.2
      left_inv := fun a => rfl
      right_inv := by
        rintro ⟨⟨i, a⟩, rfl⟩
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext a b
  simp [Matrix.toSquareBlock_def, Matrix.blockDiagonal'_apply, e]
private theorem valuation_intCast_eq_pow_padicValInt {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) (p : ℕ) [hp : Fact p.Prime]
    (hpO : ¬ IsUnit (p : O)) (a : ℤ) (ha : a ≠ 0) :
    v (a : C) = v (p : C) ^ padicValInt p a := by
  have hle : ∀ n : ℤ, v (n : C) ≤ 1 := fun n => by
    have := hv.map_le_one (n : O)
    rwa [map_intCast] at this
  have hp1 : v (p : C) < 1 := by
    have hle' : v (p : C) ≤ 1 := by exact_mod_cast hle p
    refine lt_of_le_of_ne hle' fun h => hpO ?_
    refine hv.isUnit_of_one ?_ ?_
    · rw [map_natCast]
      exact (Nat.cast_ne_zero.mpr hp.out.ne_zero).isUnit
    · rw [map_natCast]
      exact h
  obtain ⟨m, hm⟩ := padicValInt_dvd (p := p) a
  have hnd : ¬ (p : ℤ) ∣ m := by
    rintro ⟨c, hc⟩
    have h := (padicValInt_dvd_iff (p := p) (padicValInt p a + 1) a).mp
      ⟨c, by rw [pow_succ]; linear_combination hm + (p : ℤ) ^ padicValInt p a * hc⟩
    rcases h with h | h
    · exact ha h
    · omega
  have hcop : IsCoprime (p : ℤ) m :=
    (Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd.mpr hnd
  obtain ⟨x, y, hxy⟩ := hcop
  have hm1 : v (m : C) = 1 := by
    refine le_antisymm (hle m) (not_lt.mp fun hlt => ?_)
    have h1 : v ((x : C) * p) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) (hle x)) hp1
    have h2 : v ((y : C) * m) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) (hle y)) hlt
    have h3 := v.map_add_lt h1 h2
    have h4 : ((x : C) * p + y * m) = 1 := by exact_mod_cast hxy
    rw [h4, map_one] at h3
    exact lt_irrefl _ h3
  have hc : (a : C) = (p : C) ^ padicValInt p a * m := by exact_mod_cast hm
  rw [hc, map_mul, map_pow, hm1, mul_one]
private theorem discr_CMDatum_eq_prod_places_lemma_6 {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [StarRing R] {s : ℕ}
    {w : Fin s → Place p R} (h1 : ∀ i j, i ≠ j → (w i).e * (w j).e = 0)
    (h2 : (∑ i, (w i).e) + (∑ i, (w i).bar) = 1) (h3 : ∀ i j, (w i).e * (w j).bar = 0)
    (B : ∀ i, Module.Basis (Fin (w i).n) ℤ_[p] (w i).Ow) (i : Fin s) (a : Fin (w i).n) :
    (((Pi.basis B).prod (Pi.basis B)).map (UpperTheory.PlacesDiscr.splitEquiv h1 h2 h3)).reindex
        (Equiv.sigmaSumDistrib _ _).symm ⟨i, Sum.inl a⟩ = ((B i a : (w i).Ow) : ℤ_[p] ⊗[ℤ] R) ∧
    (((Pi.basis B).prod (Pi.basis B)).map (UpperTheory.PlacesDiscr.splitEquiv h1 h2 h3)).reindex
        (Equiv.sigmaSumDistrib _ _).symm ⟨i, Sum.inr a⟩ = sig p R ((B i a : (w i).Ow) : ℤ_[p] ⊗[ℤ] R) := by
  have hs : UpperTheory.PlacesDiscr.sumMap w (Pi.single i (B i a)) = ((B i a : (w i).Ow) : ℤ_[p] ⊗[ℤ] R) := by
    rw [UpperTheory.PlacesDiscr.sumMap_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  have hsplit : ∀ x y, UpperTheory.PlacesDiscr.splitEquiv h1 h2 h3 (x, y)
      = UpperTheory.PlacesDiscr.sumMap w x + sig p R (UpperTheory.PlacesDiscr.sumMap w y) := fun x y => rfl
  constructor
  · simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, Equiv.symm_symm, Equiv.sigmaSumDistrib_apply,
      Sum.map_inl, Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply, Pi.basis_apply,
      LinearMap.inl_apply]
    rw [hsplit, map_zero, map_zero, add_zero, hs]
  · simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, Equiv.symm_symm, Equiv.sigmaSumDistrib_apply,
      Sum.map_inr, Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply, Pi.basis_apply,
      LinearMap.inr_apply]
    rw [hsplit, map_zero, zero_add, hs]
end

set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
open UpperTheory.PlacesDiscr
namespace UpperTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact (¬ IsUnit (p : O))] [Algebra ℤ_[p] O]
      (s : ℕ) (w : Fin s → Place p (𝓞 E)), (∀ i j, i ≠ j → (w i).e * (w j).e = 0) → (∑ i, (w i).e) + (∑ i, (w i).bar) = 1 →
      (∀ i j, (w i).e * (w j).bar = 0) →
      2 * ∑ i, (w i).n = Module.finrank ℚ E ∧ ∀ t : ∀ i, Fin (w i).n ≃ Emb (O := O) (w i).e, ∃ vdi : Fin s → ℝ,
        (∀ i, HasVd p v (w i) (t i) (vdi i)) ∧
        ∑ i, ((w i).n : ℝ) * vdi i = (padicValInt p (NumberField.discr E) : ℝ) / 2 := by
  intro E _ _ _ p _ C _ _ _ v O _ _ hv _ _ s w h1 h2 h3
  have hfr : Module.finrank ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, NumberField.RingOfIntegers.rank]
  have hsum : 2 * ∑ i, (w i).n = Module.finrank ℚ E := by
    rw [← hfr, ← (UpperTheory.PlacesDiscr.splitEquiv h1 h2 h3).finrank_eq, Module.finrank_prod,
      Module.finrank_pi_fintype]
    simp only [Place.n.eq_1]
    ring
  refine ⟨hsum, fun t => ?_⟩
  let B : ∀ i, Module.Basis (Fin (w i).n) ℤ_[p] (w i).Ow := fun i => Module.finBasis ℤ_[p] (w i).Ow
  let A : ∀ i, Matrix (Fin (w i).n) (Fin (w i).n) O := fun i =>
    Matrix.of fun a b => tauExt (t i b : 𝓞 E →+* O) ((B i a : (w i).Ow) : ℤ_[p] ⊗[ℤ] 𝓞 E)
  have key : ∏ i, v (algebraMap O C ((A i).det ^ 2)) ^ 2 = v ((NumberField.discr E : ℤ) : C) := by
    classical
    have hO : (0 : O) ≠ 1 := fun h => (zero_ne_one : (0 : C) ≠ 1) (by simpa using congrArg (algebraMap O C) h)
    have hE : ∀ i b, tauExt (t i b : 𝓞 E →+* O) (w i).e = 1 := fun i b => (t i b).2
    have hOw : ∀ j (x : (w j).Ow), ∃ y, (w j).e * y = (x : ℤ_[p] ⊗[ℤ] 𝓞 E) := fun j x => by
      have h : (x : ℤ_[p] ⊗[ℤ] 𝓞 E) ∈ (LinearMap.mulLeft ℤ_[p] (w j).e).range := x.2
      obtain ⟨y, hy⟩ := h
      exact ⟨y, hy⟩
    have hbar : ∀ (τ : 𝓞 E →+* O) i, tauExt τ (w i).e = 1 → ∀ j, tauExt τ (w j).bar = 0 := by
      intro τ i hτ j
      have := congrArg (tauExt τ) (h3 i j)
      rwa [map_mul, hτ, one_mul, map_zero] at this
    have hoth : ∀ (τ : 𝓞 E →+* O) i, tauExt τ (w i).e = 1 → ∀ j, j ≠ i → tauExt τ (w j).e = 0 := by
      intro τ i hτ j hji
      have := congrArg (tauExt τ) (h1 i j (Ne.symm hji))
      rwa [map_mul, hτ, one_mul, map_zero] at this
    have hz1 : ∀ (τ : 𝓞 E →+* O) i, tauExt τ (w i).e = 1 → ∀ j (x : (w j).Ow),
        tauExt τ (sig p (𝓞 E) (x : ℤ_[p] ⊗[ℤ] 𝓞 E)) = 0 := by
      intro τ i hτ j x
      obtain ⟨y, hy⟩ := hOw j x
      have hb : sig p (𝓞 E) (w j).e = (w j).bar := rfl
      rw [← hy, map_mul, hb, map_mul, hbar τ i hτ j, zero_mul]
    have hz2 : ∀ (τ : 𝓞 E →+* O) i, tauExt τ (w i).e = 1 → ∀ j, j ≠ i → ∀ x : (w j).Ow,
        tauExt τ (x : ℤ_[p] ⊗[ℤ] 𝓞 E) = 0 := by
      intro τ i hτ j hji x
      obtain ⟨y, hy⟩ := hOw j x
      rw [← hy, map_mul, hoth τ i hτ j hji, zero_mul]
    have hss : ∀ (τ : 𝓞 E →+* O), (τ.comp (starRingEnd (𝓞 E))).comp (starRingEnd (𝓞 E)) = τ := by
      intro τ
      ext x
      simp [starRingEnd_apply]
    let ρ : (Σ i : Fin s, (Fin (w i).n ⊕ Fin (w i).n)) → (𝓞 E →+* O) := fun k =>
      Sum.elim (fun a => (t k.1 a : 𝓞 E →+* O)) (fun a => (t k.1 a : 𝓞 E →+* O).comp (starRingEnd (𝓞 E))) k.2
    have hsurj : ∀ τ : 𝓞 E →+* O, ∃ k, ρ k = τ := by
      intro τ
      by_contra hne
      push_neg at hne
      have he0 : ∀ i, tauExt τ (w i).e = 0 := by
        intro i
        rcases eq_zero_or_one_of_idempotent_integers hv (tauExt τ (w i).e) (by rw [← map_mul, (w i).idem]) with h | h
        · exact h
        · exfalso
          exact hne ⟨i, Sum.inl ((t i).symm ⟨τ, h⟩)⟩ (by simp [ρ])
      have hb0 : ∀ i, tauExt τ (w i).bar = 0 := by
        intro i
        have hidem : (w i).bar * (w i).bar = (w i).bar := by
          show sig p (𝓞 E) (w i).e * sig p (𝓞 E) (w i).e = sig p (𝓞 E) (w i).e
          rw [← map_mul, (w i).idem]
        rcases eq_zero_or_one_of_idempotent_integers hv (tauExt τ (w i).bar) (by rw [← map_mul, hidem]) with h | h
        · exact h
        · exfalso
          have hmem : tauExt (τ.comp (starRingEnd (𝓞 E))) (w i).e = 1 := by
            rw [tauExt_comp_star_eq_tauExt_sig]
            exact h
          refine hne ⟨i, Sum.inr ((t i).symm ⟨τ.comp (starRingEnd (𝓞 E)), hmem⟩)⟩ ?_
          simp only [ρ, Sum.elim_inr, Equiv.apply_symm_apply]
          exact hss τ
      have := congrArg (tauExt τ) h2
      rw [map_add, map_sum, map_sum, map_one] at this
      simp only [he0, hb0, Finset.sum_const_zero, add_zero] at this
      exact hO this
    have hinj : Function.Injective (UpperTheory.PlacesDiscr.restrEmb hv (E := E)) := by
      intro σ σ' h
      apply AlgHom.toLinearMap_injective
      refine (NumberField.integralBasis E).ext fun i => ?_
      simp only [AlgHom.toLinearMap_apply, NumberField.integralBasis_apply]
      have h1' := UpperTheory.PlacesDiscr.restrEmb_spec hv σ (RingOfIntegers.basis E i)
      have h2' := UpperTheory.PlacesDiscr.restrEmb_spec hv σ' (RingOfIntegers.basis E i)
      rw [h] at h1'
      exact h1'.symm.trans h2'
    have hcard : Fintype.card (E →ₐ[ℚ] C) = Fintype.card (Σ i : Fin s, (Fin (w i).n ⊕ Fin (w i).n)) := by
      rw [AlgHom.card ℚ E C, ← hsum, Fintype.card_sigma]
      simp only [Fintype.card_sum, Fintype.card_fin]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    let g : (E →ₐ[ℚ] C) → (Σ i : Fin s, (Fin (w i).n ⊕ Fin (w i).n)) := fun σ =>
      (hsurj (UpperTheory.PlacesDiscr.restrEmb hv σ)).choose
    have hg : ∀ σ, ρ (g σ) = UpperTheory.PlacesDiscr.restrEmb hv σ := fun σ =>
      (hsurj (UpperTheory.PlacesDiscr.restrEmb hv σ)).choose_spec
    have hginj : Function.Injective g := by
      intro σ σ' h
      apply hinj
      rw [← hg σ, ← hg σ', h]
    let eg := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcard⟩)
    have hρ : ∀ k, ρ k = UpperTheory.PlacesDiscr.restrEmb hv (eg.symm k) := by
      intro k
      have := hg (eg.symm k)
      have hk : g (eg.symm k) = k := eg.apply_symm_apply k
      rwa [hk] at this
    let γs := (((Pi.basis B).prod (Pi.basis B)).map (UpperTheory.PlacesDiscr.splitEquiv h1 h2 h3)).reindex
      (Equiv.sigmaSumDistrib (fun i => Fin (w i).n) (fun i => Fin (w i).n)).symm
    have hγl : ∀ i a, γs ⟨i, Sum.inl a⟩ = ((B i a : (w i).Ow) : ℤ_[p] ⊗[ℤ] 𝓞 E) :=
      fun i a => (discr_CMDatum_eq_prod_places_lemma_6 h1 h2 h3 B i a).1
    have hγr : ∀ i a, γs ⟨i, Sum.inr a⟩ = sig p (𝓞 E) ((B i a : (w i).Ow) : ℤ_[p] ⊗[ℤ] 𝓞 E) :=
      fun i a => (discr_CMDatum_eq_prod_places_lemma_6 h1 h2 h3 B i a).2
    have hblock : (Matrix.of fun m k => tauExt (ρ k) (γs m))
        = Matrix.blockDiagonal' (fun i => Matrix.fromBlocks (A i) 0 0 (A i)) := by
      ext ⟨j, u⟩ ⟨i, c⟩
      rw [Matrix.of_apply, Matrix.blockDiagonal'_apply]
      by_cases hij : j = i
      · subst hij
        rw [dif_pos rfl]
        simp only [cast_eq]
        rcases u with a | a <;> rcases c with b | b
        · rw [hγl, Matrix.fromBlocks_apply₁₁]
          rfl
        · rw [hγl, Matrix.fromBlocks_apply₁₂]
          simp only [ρ, Sum.elim_inr]
          rw [tauExt_comp_star_eq_tauExt_sig, hz1 _ j (hE j b) j (B j a), Matrix.zero_apply]
        · rw [hγr, Matrix.fromBlocks_apply₂₁]
          simp only [ρ, Sum.elim_inl]
          rw [hz1 _ j (hE j b) j (B j a), Matrix.zero_apply]
        · rw [hγr, Matrix.fromBlocks_apply₂₂]
          simp only [ρ, Sum.elim_inr]
          rw [tauExt_comp_star_eq_tauExt_sig, UpperTheory.PlacesDiscr.sig_sig]
          rfl
      · rw [dif_neg hij]
        rcases u with a | a <;> rcases c with b | b
        · rw [hγl]
          exact hz2 _ i (hE i b) j hij (B j a)
        · rw [hγl]
          simp only [ρ, Sum.elim_inr]
          rw [tauExt_comp_star_eq_tauExt_sig]
          exact hz1 _ i (hE i b) j (B j a)
        · rw [hγr]
          exact hz1 _ i (hE i b) j (B j a)
        · rw [hγr]
          simp only [ρ, Sum.elim_inr]
          rw [tauExt_comp_star_eq_tauExt_sig, UpperTheory.PlacesDiscr.sig_sig]
          exact hz2 _ i (hE i b) j hij (B j a)
    have hdetN : (Matrix.of fun m k => tauExt (ρ k) (γs m)).det = ∏ i, ((A i).det * (A i).det) := by
      rw [hblock, det_blockDiagonal'_eq_prod_det]
      simp only [Matrix.det_fromBlocks_zero₂₁]
    have hcι : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
        = Fintype.card (Σ i : Fin s, (Fin (w i).n ⊕ Fin (w i).n)) := by
      rw [← hcard, AlgHom.card ℚ E C, ← Module.finrank_eq_card_chooseBasisIndex,
        NumberField.RingOfIntegers.rank]
    let eι := Fintype.equivOfCardEq hcι
    let γ0 := (Algebra.TensorProduct.basis ℤ_[p] (RingOfIntegers.basis E)).reindex eι
    have hN0 := det_linearForms_basis_change (fun k => (tauExt (ρ k)).toLinearMap) γs γ0
    simp only [AlgHom.toLinearMap_apply] at hN0
    have hU : IsUnit (γs.toMatrix γ0).det :=
      isUnit_iff_exists_inv.mpr ⟨(γ0.toMatrix γs).det,
        by rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]⟩
    have hvU : v (algebraMap O C (algebraMap ℤ_[p] O (γs.toMatrix γ0).det)) = 1 :=
      hv.one_of_isUnit (hU.map _)
    have hD := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ C
      (NumberField.integralBasis E) (eι.trans eg.symm)
    rw [← NumberField.coe_discr, map_intCast] at hD
    have hEMR : (Algebra.embeddingsMatrixReindex ℚ C (NumberField.integralBasis E) (eι.trans eg.symm)).det
        = algebraMap O C (Matrix.of fun m k => tauExt (ρ k) (γ0 m)).det := by
      rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self eι.symm]
      congr 1
      ext m k
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, γ0, hρ,
        NumberField.integralBasis_apply, UpperTheory.PlacesDiscr.restrEmb_spec, tauExt]
    have hfin : v ((algebraMap O C (algebraMap ℤ_[p] O (γs.toMatrix γ0).det * ∏ i, ((A i).det * (A i).det))) ^ 2)
        = ∏ i, v (algebraMap O C ((A i).det ^ 2)) ^ 2 := by
      rw [map_pow, map_mul, map_mul, hvU, one_mul, map_prod, map_prod, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [sq ((A i).det)]
    rw [hD, hEMR, hN0, hdetN, hfin]
  have hdisc : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  have hvdisc := valuation_intCast_eq_pow_padicValInt hv p (Fact.out : ¬ IsUnit (p : O)) (NumberField.discr E) hdisc
  have hpC : algebraMap O C (p : O) = (p : C) := map_natCast _ _
  have hpne : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  set q : ℝ := ((v (algebraMap O C (p : O)) : NNReal) : ℝ) with hqdef
  have hq0 : 0 < q := by
    rw [hqdef, hpC, NNReal.coe_pos]
    exact lt_of_le_of_ne (zero_le') (fun h => hpne ((v.zero_iff).mp h.symm))
  have hq1 : q ≠ 1 := by
    intro h
    have h' : v (algebraMap O C (p : O)) = 1 := by
      rw [hqdef] at h
      exact_mod_cast h
    refine (Fact.out : ¬ IsUnit (p : O)) (hv.isUnit_of_one ?_ h')
    rw [hpC]
    exact hpne.isUnit
  set x : Fin s → ℝ := fun i => ((v (algebraMap O C ((A i).det ^ 2)) : NNReal) : ℝ) with hxdef
  have hprod : ∏ i, x i ^ 2 = q ^ padicValInt p (NumberField.discr E) := by
    have := congrArg (fun r : NNReal => (r : ℝ)) (key.trans hvdisc)
    simp only [NNReal.coe_prod, NNReal.coe_pow] at this
    rw [hqdef, hpC]
    exact this
  have hx0 : ∀ i, 0 < x i := by
    intro i
    have hne : ∏ i, x i ^ 2 ≠ 0 := by rw [hprod]; positivity
    have hi := (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
    have hge : 0 ≤ x i := NNReal.coe_nonneg _
    exact lt_of_le_of_ne hge (fun h => hi (by rw [← h]; ring))
  have hn : ∀ i, ((w i).n : ℝ) * (Real.logb q (x i) / (w i).n) = Real.logb q (x i) := by
    intro i
    by_cases h0 : (w i).n = 0
    · have hA : (A i).det = 1 := by
        haveI : IsEmpty (Fin (w i).n) := by rw [h0]; infer_instance
        exact Matrix.det_isEmpty
      have hx1 : x i = 1 := by
        simp only [hxdef, hA, one_pow, map_one, NNReal.coe_one]
      rw [hx1, Real.logb_one, zero_div, mul_zero]
    · have : ((w i).n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0
      field_simp
  refine ⟨fun i => Real.logb q (x i) / (w i).n, fun i => ⟨B i, ?_⟩, ?_⟩
  · show x i = q ^ (((w i).n : ℝ) * (Real.logb q (x i) / (w i).n))
    rw [hn i, Real.rpow_logb hq0 hq1 (hx0 i)]
  · simp only [hn]
    rw [← Real.logb_prod _ _ (fun i _ => (hx0 i).ne')]
    have h2 : (∏ i, x i) ^ 2 = q ^ padicValInt p (NumberField.discr E) := by
      rw [← Finset.prod_pow]; exact hprod
    have h3 : 2 * Real.logb q (∏ i, x i) = (padicValInt p (NumberField.discr E) : ℝ) := by
      have := congrArg (Real.logb q) h2
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one_iff.mpr ⟨hq0.ne', hq1, by intro h; linarith⟩] at this
      push_cast at this
      linarith
    linarith
end UpperTheory
