-- Prove2me | solution 2 for StrongConv.exists_linearEquiv_youngSpace_specht
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:15:19.014202+00:00
-- url     : https://prove2.me/submissions/b881269e-0bab-4807-bc6d-83c3afa1c978

import Mathlib
import Definitions.Def_StrongConvG4
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Theorems.Thm_OAI_Saxl_specht_irreducible

open OAI.Saxl Matrix

namespace StrongConv.W2HP

variable {N : ℕ}


/-- symmetrizer over a subgroup -/
noncomputable def symA (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)] : (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) :=
  ∑ p ∈ Finset.univ.filter (· ∈ R), MonoidAlgebra.of ℂ _ p

noncomputable def antiB (C : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ C)] : (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) :=
  ∑ q ∈ Finset.univ.filter (· ∈ C), ((Equiv.Perm.sign q : ℤ) : ℂ) • MonoidAlgebra.of ℂ _ q

theorem symA_coeff (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)] (z : (Equiv.Perm (Fin N))) :
    (symA R).coeff z = if z ∈ R then 1 else 0 := by
  classical
  unfold symA
  rw [MonoidAlgebra.coeff_sum]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finset.sum_apply',
    Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp

theorem antiB_coeff (C : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ C)] (z : (Equiv.Perm (Fin N))) :
    (antiB C).coeff z = if z ∈ C then ((Equiv.Perm.sign z : ℤ) : ℂ) else 0 := by
  classical
  unfold antiB
  rw [MonoidAlgebra.coeff_sum]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, MonoidAlgebra.coeff_single,
    Finset.sum_apply', Finsupp.single_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_ite_eq']
  simp

theorem symA_coeff_inv (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)] (z : (Equiv.Perm (Fin N))) :
    (symA R).coeff z⁻¹ = (symA R).coeff z := by
  simp [symA_coeff]

theorem antiB_coeff_inv (C : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ C)] (z : (Equiv.Perm (Fin N))) :
    (antiB C).coeff z⁻¹ = (antiB C).coeff z := by
  simp [antiB_coeff, Equiv.Perm.sign_inv]

noncomputable abbrev MR (y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) : Matrix (Equiv.Perm (Fin N)) (Equiv.Perm (Fin N)) ℂ :=
  LinearMap.toMatrix (MonoidAlgebra.basis (Equiv.Perm (Fin N)) ℂ) (MonoidAlgebra.basis (Equiv.Perm (Fin N)) ℂ) (LinearMap.mulRight ℂ y)

theorem MR_apply (y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) (i j : (Equiv.Perm (Fin N))) : MR y i j = y.coeff (j⁻¹ * i) := by
  rw [MR, LinearMap.toMatrix_apply]
  simp only [MonoidAlgebra.basis_apply, LinearMap.mulRight_apply]
  change (MonoidAlgebra.single j 1 * y).coeff i = _
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]

theorem MR_symm (y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) (hy : ∀ z, y.coeff z⁻¹ = y.coeff z) : (MR y)ᵀ = MR y := by
  ext i j
  rw [Matrix.transpose_apply, MR_apply, MR_apply, ← hy]
  simp

theorem mulRight_mul (x y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    LinearMap.mulRight ℂ (x * y) = LinearMap.mulRight ℂ y ∘ₗ LinearMap.mulRight ℂ x := by
  ext z
  simp [mul_assoc]

theorem finrank_range_mulRight (y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    Module.finrank ℂ (LinearMap.range (LinearMap.mulRight ℂ y)) = (MR y).rank := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin (MR y) (MonoidAlgebra.basis (Equiv.Perm (Fin N)) ℂ) (MonoidAlgebra.basis (Equiv.Perm (Fin N)) ℂ),
    Matrix.toLin_toMatrix]

theorem finrank_range_swap (x y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) (hx : ∀ z, x.coeff z⁻¹ = x.coeff z)
    (hy : ∀ z, y.coeff z⁻¹ = y.coeff z) :
    Module.finrank ℂ (LinearMap.range (LinearMap.mulRight ℂ (x * y))) =
      Module.finrank ℂ (LinearMap.range (LinearMap.mulRight ℂ (y * x))) := by
  have hc : ∀ u v : (MonoidAlgebra ℂ (Equiv.Perm (Fin N))), MR (u * v) = MR v * MR u := fun u v => by
    rw [MR, mulRight_mul, LinearMap.toMatrix_comp (MonoidAlgebra.basis (Equiv.Perm (Fin N)) ℂ)
      (MonoidAlgebra.basis (Equiv.Perm (Fin N)) ℂ) (MonoidAlgebra.basis (Equiv.Perm (Fin N)) ℂ)]
  rw [finrank_range_mulRight, finrank_range_mulRight, hc, hc, ← Matrix.rank_transpose,
    Matrix.transpose_mul]
  change ((MR x)ᵀ * (MR y)ᵀ).rank = (MR x * MR y).rank
  rw [MR_symm x hx, MR_symm y hy]

theorem sum_mul_left_mem {M : Type*} [AddCommMonoid M] (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)]
    (p : (Equiv.Perm (Fin N))) (hp : p ∈ R) (f : (Equiv.Perm (Fin N)) → M) :
    ∑ q ∈ Finset.univ.filter (· ∈ R), f (p * q) = ∑ q ∈ Finset.univ.filter (· ∈ R), f q := by
  refine Finset.sum_nbij' (fun q => p * q) (fun q => p⁻¹ * q) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact R.mul_mem hp hq
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact R.mul_mem (R.inv_mem hp) hq
  · intro q _; simp
  · intro q _; simp
  · intro q _; rfl

theorem symA_mul_self (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)] :
    symA R * symA R = ((Finset.univ.filter (· ∈ R)).card : ℂ) • symA R := by
  nth_rewrite 1 [symA]
  rw [Finset.sum_mul]
  have h : ∀ p ∈ Finset.univ.filter (· ∈ R),
      MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) p * symA R = symA R := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [symA, Finset.mul_sum]
    simp_rw [← map_mul]
    exact sum_mul_left_mem R p hp (fun q => MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) q)
  rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.cast_smul_eq_nsmul]

variable {μ : YoungDiagram}

noncomputable def e0 (T : Tableau N μ) : WordSpace N (μ.colLen 0) := Pi.single (rowWord T) 1

noncomputable def actL (T : Tableau N μ) : (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) →ₗ[ℂ] WordSpace N (μ.colLen 0) where
  toFun x := (wordRep N (μ.colLen 0)).asAlgebraHom x (e0 T)
  map_add' x y := by simp
  map_smul' c x := by simp

theorem actL_apply (T : Tableau N μ) (x : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    actL T x = (wordRep N (μ.colLen 0)).asAlgebraHom x (e0 T) := rfl

theorem actL_mul (T : Tableau N μ) (x y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    actL T (x * y) = (wordRep N (μ.colLen 0)).asAlgebraHom x (actL T y) := by
  simp [actL_apply, map_mul]

theorem actL_of (T : Tableau N μ) (g : (Equiv.Perm (Fin N))) :
    actL T (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) g) = wordRep N (μ.colLen 0) g (e0 T) := by
  simp [actL_apply]

theorem asAlg_mem {d : ℕ} (P : Subrepresentation (wordRep N d)) (x : (MonoidAlgebra ℂ (Equiv.Perm (Fin N))))
    {v : WordSpace N d} (hv : v ∈ P.toSubmodule) :
    (wordRep N d).asAlgebraHom x v ∈ P.toSubmodule := by
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [Representation.asAlgebraHom_of]; exact P.apply_mem_toSubmodule g hv
  | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact P.toSubmodule.add_mem hx hy
  | smul c x hx => rw [map_smul, LinearMap.smul_apply]; exact P.toSubmodule.smul_mem c hx

theorem wordRep_e0 (T : Tableau N μ) (g : (Equiv.Perm (Fin N))) :
    wordRep N (μ.colLen 0) g (e0 T) = Pi.single (rowWord T ∘ ⇑g⁻¹) 1 := by
  rw [e0, wordRep_single]

theorem asAlg_symA_e0 (T : Tableau N μ) (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)]
    (hR : ∀ p : (Equiv.Perm (Fin N)), rowWord T ∘ ⇑p = rowWord T ↔ p ∈ R) :
    (wordRep N (μ.colLen 0)).asAlgebraHom (symA R) (e0 T) =
      ((Finset.univ.filter (· ∈ R)).card : ℂ) • e0 T := by
  rw [symA, map_sum, LinearMap.sum_apply]
  have h : ∀ p ∈ Finset.univ.filter (· ∈ R),
      (wordRep N (μ.colLen 0)).asAlgebraHom (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) p) (e0 T) = e0 T := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Representation.asAlgebraHom_of, wordRep_e0, (hR _).2 (R.inv_mem hp)]
    rfl
  rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem asAlg_antiB_e0 (T : Tableau N μ) [DecidablePred (· ∈ columnGroup T)] :
    (wordRep N (μ.colLen 0)).asAlgebraHom (antiB (columnGroup T)) (e0 T) = polytabloid T := by
  classical
  rw [antiB, map_sum, LinearMap.sum_apply, polytabloid]
  simp only [map_smul, LinearMap.smul_apply, Representation.asAlgebraHom_of]
  rw [Finset.sum_subtype (Finset.univ.filter (· ∈ columnGroup T)) (p := (· ∈ columnGroup T))
    (by simp)]
  rfl

theorem actL_of_eval (T : Tableau N μ) (g : (Equiv.Perm (Fin N))) :
    actL T (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) g) (rowWord T) =
      if rowWord T ∘ ⇑g = rowWord T then 1 else 0 := by
  rw [actL_of]
  change (Pi.single (rowWord T) 1 : WordSpace N (μ.colLen 0)) (rowWord T ∘ ⇑g) = _
  rw [Pi.single_apply]

theorem eval_key (T : Tableau N μ) (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)]
    (hR : ∀ p : (Equiv.Perm (Fin N)), rowWord T ∘ ⇑p = rowWord T ↔ p ∈ R) (h : (Equiv.Perm (Fin N))) (y : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    actL T (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) h⁻¹ * y) (rowWord T) = (y * symA R).coeff h := by
  induction y using MonoidAlgebra.induction_on with
  | of g =>
    rw [← map_mul, actL_of_eval, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
      one_mul, symA_coeff]
    have : h⁻¹ * g ∈ R ↔ g⁻¹ * h ∈ R := by
      rw [← R.inv_mem_iff]; simp
    by_cases hg : g⁻¹ * h ∈ R
    · rw [if_pos ((hR _).2 (this.2 hg)), if_pos hg]
    · rw [if_neg (fun e => hg (this.1 ((hR _).1 e))), if_neg hg]
  | add x y hx hy =>
    rw [mul_add, map_add, Pi.add_apply, hx, hy, add_mul, MonoidAlgebra.coeff_add,
      Finsupp.add_apply]
  | smul c x hx =>
    rw [mul_smul_comm, map_smul, Pi.smul_apply, hx, smul_mul_assoc, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply]

theorem eval_ab (T : Tableau N μ) (R C : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)]
    [DecidablePred (· ∈ C)]
    (hR : ∀ p : (Equiv.Perm (Fin N)), rowWord T ∘ ⇑p = rowWord T ↔ p ∈ R) (hRC : ∀ q, q ∈ R → q ∈ C → q = 1) :
    actL T (symA R * antiB C) (rowWord T) = ((Finset.univ.filter (· ∈ R)).card : ℂ) := by
  rw [symA, antiB, Finset.sum_mul_sum, map_sum, Finset.sum_apply]
  have h : ∀ p ∈ Finset.univ.filter (· ∈ R),
      actL T (∑ q ∈ Finset.univ.filter (· ∈ C),
        MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) p * (((Equiv.Perm.sign q : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) q))
        (rowWord T) = 1 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [map_sum, Finset.sum_apply]
    have h2 : ∀ q ∈ Finset.univ.filter (· ∈ C),
        actL T (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) p * (((Equiv.Perm.sign q : ℤ) : ℂ) •
          MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) q)) (rowWord T) = if q = 1 then 1 else 0 := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [mul_smul_comm, ← map_mul, map_smul, Pi.smul_apply, actL_of_eval]
      have hw : rowWord T ∘ ⇑(p * q) = rowWord T ∘ ⇑q := by
        rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, (hR p).2 hp]
      rw [hw]
      by_cases hq1 : q = 1
      · subst hq1; simp
      · rw [if_neg hq1, if_neg (fun e => hq1 (hRC q ((hR q).1 e) hq)), smul_zero]
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq']
    simp [C.one_mem]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem card_ne_zero (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)] :
    ((Finset.univ.filter (· ∈ R)).card : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨1, by simp [R.one_mem]⟩

theorem inj_mul_symA (T : Tableau N μ) (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)]
    (hR : ∀ p : (Equiv.Perm (Fin N)), rowWord T ∘ ⇑p = rowWord T ↔ p ∈ R) (x : (MonoidAlgebra ℂ (Equiv.Perm (Fin N))))
    (hx : actL T (x * symA R) = 0) : x * symA R = 0 := by
  have h1 : x * symA R * symA R = 0 := by
    apply MonoidAlgebra.coeff_injective
    ext h
    rw [← eval_key T R hR h, actL_mul, hx, map_zero]
    rfl
  rw [mul_assoc, symA_mul_self, mul_smul_comm, smul_eq_zero] at h1
  exact h1.resolve_left (card_ne_zero R)

theorem youngSpace_eq (c : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    (Submodule.span (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) {c}).restrictScalars ℂ = LinearMap.range (LinearMap.mulRight ℂ c) := by
  ext x
  simp only [Submodule.restrictScalars_mem, Submodule.mem_span_singleton, LinearMap.mem_range,
    LinearMap.mulRight_apply, smul_eq_mul]

section main

variable (t T : Tableau N μ) (R : Subgroup (Equiv.Perm (Fin N))) [DecidablePred (· ∈ R)]
  [DecidablePred (· ∈ columnGroup T)]

theorem actL_mem_of_ab (hmem : polytabloid T ∈ spechtSub t) (z : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    actL T (z * (symA R * antiB (columnGroup T))) ∈ Specht t := by
  rw [actL_mul, actL_mul, actL_apply, asAlg_antiB_e0]
  exact asAlg_mem _ z (asAlg_mem _ _ hmem)

theorem actL_mem_of_ba (hR : ∀ p : (Equiv.Perm (Fin N)), rowWord T ∘ ⇑p = rowWord T ↔ p ∈ R)
    (hmem : polytabloid T ∈ spechtSub t) (z : (MonoidAlgebra ℂ (Equiv.Perm (Fin N)))) :
    actL T (z * (antiB (columnGroup T) * symA R)) ∈ Specht t := by
  rw [actL_mul, actL_mul, actL_apply, asAlg_symA_e0 T R hR, map_smul, asAlg_antiB_e0]
  exact asAlg_mem _ z ((spechtSub t).toSubmodule.smul_mem _ hmem)

theorem finrank_ba_le (hR : ∀ p : (Equiv.Perm (Fin N)), rowWord T ∘ ⇑p = rowWord T ↔ p ∈ R)
    (hmem : polytabloid T ∈ spechtSub t) :
    Module.finrank ℂ (LinearMap.range (LinearMap.mulRight ℂ (antiB (columnGroup T) * symA R))) ≤
      Module.finrank ℂ (Specht t) := by
  set S := LinearMap.range (LinearMap.mulRight ℂ (antiB (columnGroup T) * symA R))
  let ψ : S →ₗ[ℂ] Specht t := (actL T ∘ₗ S.subtype).codRestrict (Specht t) (by
    rintro ⟨x, z, rfl⟩
    exact actL_mem_of_ba t T R hR hmem z)
  apply LinearMap.finrank_le_finrank_of_injective (f := ψ)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, z, rfl⟩ hx
  have h0 : actL T (z * antiB (columnGroup T) * symA R) = 0 := by
    have := congrArg Subtype.val hx
    simpa [ψ, mul_assoc] using this
  have := inj_mul_symA T R hR _ h0
  apply Subtype.ext
  simpa [mul_assoc] using this

theorem main_generic (hR : ∀ p : Equiv.Perm (Fin N), rowWord T ∘ ⇑p = rowWord T ↔ p ∈ R)
    (hRC : ∀ q, q ∈ R → q ∈ columnGroup T → q = 1)
    (hc : youngSymmetrizer N μ.rowLens = symA R * antiB (columnGroup T))
    (hmem : polytabloid T ∈ spechtSub t) :
    ∃ e : youngSpace N μ.rowLens ≃ₗ[ℂ] Specht t,
      ∀ (σ : Equiv.Perm (Fin N)) (x : youngSpace N μ.rowLens),
        e (youngAct N μ.rowLens σ x) = spechtRep t σ (e x) := by
  have hY : youngSpace N μ.rowLens =
      LinearMap.range (LinearMap.mulRight ℂ (symA R * antiB (columnGroup T))) := by
    rw [youngSpace, youngSpace_eq, hc]
  let φ : youngSpace N μ.rowLens →ₗ[ℂ] Specht t :=
    (actL T ∘ₗ (youngSpace N μ.rowLens).subtype).codRestrict (Specht t) (by
      rintro ⟨x, hx⟩
      rw [hY] at hx
      obtain ⟨z, rfl⟩ := hx
      exact actL_mem_of_ab t T R hmem z)
  have hφ : ∀ x, (φ x : WordSpace N (μ.colLen 0)) = actL T x := fun x => rfl
  have hequiv : ∀ (σ : Equiv.Perm (Fin N)) (x : youngSpace N μ.rowLens),
      φ (youngAct N μ.rowLens σ x) = spechtRep t σ (φ x) := by
    intro σ x
    apply Subtype.ext
    rw [hφ]
    change actL T (MonoidAlgebra.of ℂ _ σ * (x : (MonoidAlgebra ℂ (Equiv.Perm (Fin N))))) = wordRep N (μ.colLen 0) σ (actL T x)
    rw [actL_mul, Representation.asAlgebraHom_of]
  -- the image is a subrepresentation
  let P : Subrepresentation (spechtRep t) :=
    { toSubmodule := LinearMap.range φ
      apply_mem_toSubmodule := by
        rintro σ _ ⟨x, rfl⟩
        exact ⟨youngAct N μ.rowLens σ x, hequiv σ x⟩ }
  have hc_mem : symA R * antiB (columnGroup T) ∈ youngSpace N μ.rowLens := by
    rw [hY]; exact ⟨1, one_mul _⟩
  have hne : φ ⟨_, hc_mem⟩ ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Specht t => (v : WordSpace N (μ.colLen 0)) (rowWord T)) h0
    simp only [hφ, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
    rw [eval_ab T R (columnGroup T) hR hRC] at h1
    exact card_ne_zero R h1
  have hsurj : Function.Surjective φ := by
    have := OAI.Saxl.specht_irreducible t
    rcases eq_bot_or_eq_top P with hP | hP
    · exfalso
      apply hne
      have : φ ⟨_, hc_mem⟩ ∈ P.toSubmodule := ⟨_, rfl⟩
      rw [hP] at this
      exact this
    · rw [← LinearMap.range_eq_top]
      exact congrArg Subrepresentation.toSubmodule hP
  have hdim : Module.finrank ℂ (youngSpace N μ.rowLens) ≤ Module.finrank ℂ (Specht t) := by
    rw [hY, finrank_range_swap _ _ (symA_coeff_inv R) (antiB_coeff_inv _)]
    exact finrank_ba_le t T R hR hmem
  have hdim' : Module.finrank ℂ (Specht t) ≤ Module.finrank ℂ (youngSpace N μ.rowLens) := by
    have := LinearMap.finrank_range_le φ
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hdim hdim')).2 hsurj
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, hequiv⟩

end main

/-! ## The canonical tableau -/

theorem tabRow_cons (r : ℕ) (rows : List ℕ) (x : ℕ) :
    tabRow (r :: rows) x = if r ≤ x then tabRow rows (x - r) + 1 else 0 := by
  unfold tabRow
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  have h0 : (List.take (0 + 1) (r :: rows)).sum = r := by simp
  by_cases h : r ≤ x
  · have hp : ((fun i => decide ((List.take (i + 1) (r :: rows)).sum ≤ x)) ∘ Nat.succ) =
        fun i => decide ((rows.take (i+1)).sum ≤ x - r) := by
      funext i
      show decide ((List.take (i + 1 + 1) (r :: rows)).sum ≤ x) = _
      rw [List.take_succ_cons, List.sum_cons]
      simp only [decide_eq_decide]
      omega
    rw [hp, h0, if_pos (by simpa using h), if_pos h, List.length_cons, List.length_map]
  · have hp : ((fun i => decide ((List.take (i + 1) (r :: rows)).sum ≤ x)) ∘ Nat.succ) =
        fun _ => false := by
      funext i
      show decide ((List.take (i + 1 + 1) (r :: rows)).sum ≤ x) = _
      rw [List.take_succ_cons, List.sum_cons]
      simp only [decide_eq_false_iff_not]
      omega
    rw [hp, h0, if_neg (by simpa using h), if_neg h, List.length_map]
    simp

theorem tabCol_cons (r : ℕ) (rows : List ℕ) (x : ℕ) :
    tabCol (r :: rows) x = if r ≤ x then tabCol rows (x - r) else x := by
  unfold tabCol
  rw [tabRow_cons]
  split_ifs with h
  · simp only [List.take_succ_cons, List.sum_cons]
    omega
  · simp

theorem tab_spec (rows : List ℕ) (x : ℕ) (hx : x < rows.sum) :
    ∃ h : tabRow rows x < rows.length, tabCol rows x < rows[tabRow rows x] ∧
      (rows.take (tabRow rows x)).sum + tabCol rows x = x := by
  induction rows generalizing x with
  | nil => simp at hx
  | cons r rows ih =>
    simp only [List.sum_cons] at hx
    by_cases h : r ≤ x
    · obtain ⟨h1, h2, h3⟩ := ih (x - r) (by omega)
      have e1 := tabRow_cons r rows x
      have e2 := tabCol_cons r rows x
      rw [if_pos h] at e1 e2
      refine ⟨by rw [e1]; simp; omega, ?_, ?_⟩
      · simp only [e1, e2, List.getElem_cons_succ]; exact h2
      · rw [e1, e2, List.take_succ_cons, List.sum_cons]; omega
    · have e1 := tabRow_cons r rows x
      have e2 := tabCol_cons r rows x
      rw [if_neg h] at e1 e2
      refine ⟨by rw [e1]; simp, ?_, ?_⟩
      · simp only [e1, e2, List.getElem_cons_zero]; omega
      · rw [e1, e2]; simp


def rowCellEquiv' (μ : YoungDiagram) : μ.cells ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun c := ⟨⟨c.val.1, YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.property)⟩,
    ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩
  invFun c := ⟨(c.1.val, c.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr c.2.isLt⟩
  left_inv c := Subtype.ext rfl
  right_inv c := by rcases c with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; rfl

theorem card_eq_sum_rowLens' (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  classical
  have h := Fintype.card_congr (rowCellEquiv' μ)
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fin] at h
  change μ.card = ∑ x : Fin (μ.colLen 0), μ.rowLen x at h
  rw [h, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range]
  have he : (List.range (μ.colLen 0)).toFinset = Finset.range (μ.colLen 0) := by
    ext i; simp
  rw [he]
  exact Fin.sum_univ_eq_sum_range μ.rowLen (μ.colLen 0)

theorem canon_mem (μ : YoungDiagram) (hN : μ.card = N) (x : Fin N) :
    (tabRow μ.rowLens x, tabCol μ.rowLens x) ∈ μ.cells := by
  obtain ⟨h1, h2, -⟩ := tab_spec μ.rowLens x (by rw [← card_eq_sum_rowLens', hN]; exact x.2)
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
  rw [YoungDiagram.get_rowLens] at h2
  exact h2

def canonMap (μ : YoungDiagram) (hN : μ.card = N) (x : Fin N) : μ.cells :=
  ⟨(tabRow μ.rowLens x, tabCol μ.rowLens x), canon_mem μ hN x⟩

theorem canonMap_injective (μ : YoungDiagram) (hN : μ.card = N) :
    Function.Injective (canonMap μ hN) := by
  intro x y hxy
  have h := congrArg Subtype.val hxy
  simp only [canonMap, Prod.mk.injEq] at h
  have hx := (tab_spec μ.rowLens x (by rw [← card_eq_sum_rowLens', hN]; exact x.2)).2.2
  have hy := (tab_spec μ.rowLens y (by rw [← card_eq_sum_rowLens', hN]; exact y.2)).2.2
  rw [h.1, h.2] at hx
  exact Fin.ext (hx.symm.trans hy)

noncomputable def canonT (μ : YoungDiagram) (hN : μ.card = N) : Tableau N μ :=
  Equiv.ofBijective (canonMap μ hN) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨canonMap_injective μ hN, by simp [hN]⟩)

def rowSub (rows : List ℕ) : Subgroup (Equiv.Perm (Fin N)) where
  carrier := {p | ∀ x : Fin N, tabRow rows (p x : ℕ) = tabRow rows (x : ℕ)}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ x)
    simpa using h.symm

instance (rows : List ℕ) : DecidablePred (· ∈ (rowSub rows : Subgroup (Equiv.Perm (Fin N)))) :=
  fun p => inferInstanceAs (Decidable (∀ x : Fin N, tabRow rows (p x : ℕ) = tabRow rows (x : ℕ)))

theorem canon_hR (μ : YoungDiagram) (hN : μ.card = N) (p : Equiv.Perm (Fin N)) :
    rowWord (canonT μ hN) ∘ ⇑p = rowWord (canonT μ hN) ↔ p ∈ rowSub μ.rowLens := by
  rw [funext_iff]
  change _ ↔ ∀ x : Fin N, _
  refine forall_congr' fun x => ?_
  rw [Fin.ext_iff]
  rfl

theorem canon_hRC (μ : YoungDiagram) (hN : μ.card = N) (q : Equiv.Perm (Fin N))
    (h1 : q ∈ rowSub μ.rowLens) (h2 : q ∈ columnGroup (canonT μ hN)) : q = 1 := by
  ext x
  have := (canonT μ hN).injective (a₁ := q x) (a₂ := x) (Subtype.ext (Prod.ext (h1 x) (h2 x)))
  rw [this]; rfl

theorem canon_hc (μ : YoungDiagram) (hN : μ.card = N)
    [DecidablePred (· ∈ columnGroup (canonT μ hN))] :
    youngSymmetrizer N μ.rowLens = symA (rowSub μ.rowLens) * antiB (columnGroup (canonT μ hN)) := by
  unfold youngSymmetrizer symA antiB
  refine congrArg₂ (· * ·) rfl ?_
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

end StrongConv.W2HP

theorem StrongConv.W2HP.bridge_dev {N : ℕ} {μ : YoungDiagram} (t : OAI.Saxl.Tableau N μ) :
    ∃ e : StrongConv.youngSpace N μ.rowLens ≃ₗ[ℂ] OAI.Saxl.Specht t,
      ∀ (σ : Equiv.Perm (Fin N)) (x : StrongConv.youngSpace N μ.rowLens),
        e (StrongConv.youngAct N μ.rowLens σ x) = OAI.Saxl.spechtRep t σ (e x) := by
  classical
  have hN : μ.card = N := by
    have := Fintype.card_congr t
    simpa using this.symm
  exact StrongConv.W2HP.main_generic t (StrongConv.W2HP.canonT μ hN)
    (StrongConv.W2HP.rowSub μ.rowLens) (StrongConv.W2HP.canon_hR μ hN)
    (StrongConv.W2HP.canon_hRC μ hN) (StrongConv.W2HP.canon_hc μ hN)
    (OAI.Saxl.polytabloid_mem_all t (StrongConv.W2HP.canonT μ hN))

theorem solution {N : ℕ} {μ : YoungDiagram} (t : OAI.Saxl.Tableau N μ) :
    ∃ e : StrongConv.youngSpace N μ.rowLens ≃ₗ[ℂ] OAI.Saxl.Specht t,
      ∀ (σ : Equiv.Perm (Fin N)) (x : StrongConv.youngSpace N μ.rowLens),
        e (StrongConv.youngAct N μ.rowLens σ x) = OAI.Saxl.spechtRep t σ (e x) :=
  StrongConv.W2HP.bridge_dev t
