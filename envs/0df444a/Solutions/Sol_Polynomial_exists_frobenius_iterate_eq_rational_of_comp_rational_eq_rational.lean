-- Prove2me | solution 1 for Polynomial.exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6be17467-7643-5cdc-aa1b-57d8dccf7762

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational

open Polynomial

namespace PolyFrobDescent

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def enum {D : ℕ} (R : Multiset k) : Fin D → k := fun i => R.toList.getD i 0

theorem enum_spec {D : ℕ} (R : Multiset k) (hR : R.card = D) :
    (Finset.univ.val.map (enum (D := D) R)) = R := by
  rw [Fin.univ_val_map]
  have hlen : R.toList.length = D := by rw [Multiset.length_toList, hR]
  have : List.ofFn (enum (D := D) R) = R.toList := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h₁ h₂
      rw [List.getElem_ofFn]
      simp only [enum]
      rw [List.getD_eq_getElem]
  rw [this, Multiset.coe_toList]

theorem enum_mem {D : ℕ} (R : Multiset k) (hR : R.card = D) (i : Fin D) :
    enum (D := D) R i ∈ R := by
  have h := congrArg (fun s : Multiset k => enum (D := D) R i ∈ s) (enum_spec R hR)
  simp only [eq_iff_iff] at h
  rw [← h, Multiset.mem_map]
  exact ⟨i, Finset.mem_univ_val i, rfl⟩

section Symm

variable (F)

noncomputable def term (D : ℕ) (gn gd : F[X]) (i : Fin D) :
    Polynomial (MvPolynomial (Fin D) F) :=
  Polynomial.C (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin D) F) gd) * Polynomial.X -
    Polynomial.C (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin D) F) gn)

noncomputable def E (D : ℕ) (gn gd : F[X]) : Polynomial (MvPolynomial (Fin D) F) :=
  ∏ i : Fin D, term F D gn gd i

variable {F}

theorem map_term {A : Type*} [CommRing A] [Algebra F A] (D : ℕ) (gn gd : F[X])
    (φ : MvPolynomial (Fin D) F →ₐ[F] A) (i : Fin D) :
    (term F D gn gd i).map (φ : MvPolynomial (Fin D) F →+* A) =
      Polynomial.C (Polynomial.aeval (φ (MvPolynomial.X i)) gd) * Polynomial.X -
        Polynomial.C (Polynomial.aeval (φ (MvPolynomial.X i)) gn) := by
  simp only [term, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    RingHom.coe_coe, Polynomial.aeval_algHom_apply]

theorem map_E {A : Type*} [CommRing A] [Algebra F A] (D : ℕ) (gn gd : F[X])
    (φ : MvPolynomial (Fin D) F →ₐ[F] A) :
    (E F D gn gd).map (φ : MvPolynomial (Fin D) F →+* A) =
      ∏ i : Fin D, (Polynomial.C (Polynomial.aeval (φ (MvPolynomial.X i)) gd) * Polynomial.X -
        Polynomial.C (Polynomial.aeval (φ (MvPolynomial.X i)) gn)) := by
  simp only [E, Polynomial.map_prod, map_term]

theorem E_coeff_isSymmetric (D : ℕ) (gn gd : F[X]) (j : ℕ) :
    MvPolynomial.IsSymmetric ((E F D gn gd).coeff j) := by
  intro e
  have h1 : (MvPolynomial.rename e) ((E F D gn gd).coeff j) =
      ((E F D gn gd).map ((MvPolynomial.rename e : MvPolynomial (Fin D) F →ₐ[F]
        MvPolynomial (Fin D) F) : MvPolynomial (Fin D) F →+* MvPolynomial (Fin D) F)).coeff j := by
    rw [Polynomial.coeff_map, RingHom.coe_coe]
  rw [h1, map_E]
  simp only [MvPolynomial.rename_X]
  refine congrArg (fun p => Polynomial.coeff p j) ?_
  rw [E]
  exact Equiv.prod_comp e (term F D gn gd)

theorem exists_q (D : ℕ) (gn gd : F[X]) (j : ℕ) :
    ∃ q : MvPolynomial (Fin D) F,
      MvPolynomial.aeval (fun i : Fin D => MvPolynomial.esymm (Fin D) F (i + 1)) q =
        (E F D gn gd).coeff j := by
  have hsurj := MvPolynomial.esymmAlgHom_surjective (σ := Fin D) (R := F) (n := D)
    (by simp)
  obtain ⟨q, hq⟩ := hsurj ⟨(E F D gn gd).coeff j, E_coeff_isSymmetric D gn gd j⟩
  refine ⟨q, ?_⟩
  have := congrArg Subtype.val hq
  rw [MvPolynomial.esymmAlgHom_apply] at this
  exact this

theorem aeval_E_coeff_of_const (D : ℕ) (gn gd : F[X]) (α : Fin D → k) (c : k)
    (hα : ∀ i, Polynomial.aeval (α i) gd ≠ 0 ∧
      Polynomial.aeval (α i) gn / Polynomial.aeval (α i) gd = c) (j : ℕ) :
    MvPolynomial.aeval α ((E F D gn gd).coeff j) =
      (∏ i, Polynomial.aeval (α i) gd) * ((Polynomial.X - Polynomial.C c) ^ D).coeff j := by
  have h1 : MvPolynomial.aeval α ((E F D gn gd).coeff j) =
      ((E F D gn gd).map ((MvPolynomial.aeval α : MvPolynomial (Fin D) F →ₐ[F] k) :
        MvPolynomial (Fin D) F →+* k)).coeff j := by
    rw [Polynomial.coeff_map]; rfl
  rw [h1, map_E]
  simp only [MvPolynomial.aeval_X]
  have h2 : ∀ i, Polynomial.C (Polynomial.aeval (α i) gd) * Polynomial.X -
      Polynomial.C (Polynomial.aeval (α i) gn) =
        Polynomial.C (Polynomial.aeval (α i) gd) * (Polynomial.X - Polynomial.C c) := by
    intro i
    obtain ⟨hd, hc⟩ := hα i
    have : Polynomial.aeval (α i) gn = c * Polynomial.aeval (α i) gd := by
      rw [← hc, div_mul_cancel₀ _ hd]
    rw [this, Polynomial.C_mul, mul_sub]
    ring
  simp_rw [h2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← map_prod Polynomial.C, Polynomial.coeff_C_mul]

theorem aeval_q (D : ℕ) (q : MvPolynomial (Fin D) F) (α : Fin D → k) :
    MvPolynomial.aeval α
        (MvPolynomial.aeval (fun i : Fin D => MvPolynomial.esymm (Fin D) F (i + 1)) q) =
      MvPolynomial.aeval (fun i : Fin D => ((Finset.univ.val.map α).esymm (i + 1) : k)) q := by
  have h := MvPolynomial.comp_aeval (fun i : Fin D => MvPolynomial.esymm (Fin D) F (i + 1))
    (MvPolynomial.aeval α : MvPolynomial (Fin D) F →ₐ[F] k)
  have h' := DFunLike.congr_fun h q
  simp only [AlgHom.comp_apply] at h'
  rw [h']
  have hf : (fun i : Fin D => (MvPolynomial.aeval α) (MvPolynomial.esymm (Fin D) F (i + 1))) =
      fun i : Fin D => ((Finset.univ.val.map α).esymm (i + 1) : k) := by
    funext i
    exact MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin D) F (i + 1) α
  rw [hf]

end Symm

section Pencil

variable (k)

noncomputable def ell (D : ℕ) (fn fd : F[X]) : F[X] :=
  Polynomial.C (fn.coeff D) - Polynomial.X * Polynomial.C (fd.coeff D)

noncomputable def sig (D : ℕ) (fn fd : F[X]) (i : Fin D) : F[X] :=
  Polynomial.C ((-1) ^ ((i : ℕ) + 1)) *
    (Polynomial.C (fn.coeff (D - (i + 1))) - Polynomial.X * Polynomial.C (fd.coeff (D - (i + 1))))

noncomputable def Phi (fn fd : F[X]) (u : k) : k[X] :=
  fn.map (algebraMap F k) - Polynomial.C u * fd.map (algebraMap F k)

variable {k}

theorem Phi_coeff (fn fd : F[X]) (u : k) (n : ℕ) :
    (Phi k fn fd u).coeff n = algebraMap F k (fn.coeff n) - u * algebraMap F k (fd.coeff n) := by
  simp [Phi, Polynomial.coeff_map]

theorem aeval_ell (D : ℕ) (fn fd : F[X]) (u : k) :
    Polynomial.aeval u (ell D fn fd) = (Phi k fn fd u).coeff D := by
  rw [Phi_coeff]
  simp only [ell, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]

theorem aeval_sig (D : ℕ) (fn fd : F[X]) (u : k) (i : Fin D) :
    Polynomial.aeval u (sig D fn fd i) =
      (-1) ^ ((i : ℕ) + 1) * (Phi k fn fd u).coeff (D - (i + 1)) := by
  rw [Phi_coeff]
  simp only [sig, map_sub, map_mul, map_pow, map_neg, map_one, Polynomial.aeval_C,
    Polynomial.aeval_X]

theorem Phi_natDegree_le (fn fd : F[X]) (u : k) (D : ℕ) (hn : fn.natDegree ≤ D)
    (hd : fd.natDegree ≤ D) : (Phi k fn fd u).natDegree ≤ D := by
  unfold Phi
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact Polynomial.natDegree_map_le.trans hn
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_map_le.trans hd)

theorem Phi_natDegree_eq (fn fd : F[X]) (u : k) (D : ℕ) (hn : fn.natDegree ≤ D)
    (hd : fd.natDegree ≤ D) (hu : Polynomial.aeval u (ell D fn fd) ≠ 0) :
    (Phi k fn fd u).natDegree = D := by
  refine le_antisymm (Phi_natDegree_le fn fd u D hn hd) ?_
  apply Polynomial.le_natDegree_of_ne_zero
  rwa [← aeval_ell]

theorem Phi_ne_zero (fn fd : F[X]) (u : k) (D : ℕ)
    (hu : Polynomial.aeval u (ell D fn fd) ≠ 0) : Phi k fn fd u ≠ 0 := by
  intro h
  apply hu
  rw [aeval_ell, h, Polynomial.coeff_zero]

theorem Phi_leadingCoeff (fn fd : F[X]) (u : k) (D : ℕ) (hn : fn.natDegree ≤ D)
    (hd : fd.natDegree ≤ D) (hu : Polynomial.aeval u (ell D fn fd) ≠ 0) :
    (Phi k fn fd u).leadingCoeff = Polynomial.aeval u (ell D fn fd) := by
  rw [Polynomial.leadingCoeff, Phi_natDegree_eq fn fd u D hn hd hu, aeval_ell]

theorem esymm_roots_Phi [IsAlgClosed k] (fn fd : F[X]) (u : k) (D : ℕ)
    (hn : fn.natDegree ≤ D) (hd : fd.natDegree ≤ D)
    (hu : Polynomial.aeval u (ell D fn fd) ≠ 0) (i : Fin D) :
    (Phi k fn fd u).roots.esymm (i + 1) =
      Polynomial.aeval u (sig D fn fd i) / Polynomial.aeval u (ell D fn fd) := by
  have hD := Phi_natDegree_eq fn fd u D hn hd hu
  have hcard : (Phi k fn fd u).roots.card = (Phi k fn fd u).natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hi : (i : ℕ) + 1 ≤ D := i.isLt
  have hk : D - (i + 1) ≤ (Phi k fn fd u).natDegree := by rw [hD]; exact Nat.sub_le _ _
  have hv := Polynomial.coeff_eq_esymm_roots_of_card hcard hk
  rw [hD, Nat.sub_sub_self hi, Phi_leadingCoeff fn fd u D hn hd hu] at hv
  rw [eq_div_iff hu, aeval_sig, hv]
  rcases neg_one_pow_eq_or k ((i : ℕ) + 1) with h | h <;> rw [h] <;> ring

theorem root_Phi (fn fd : F[X]) (hcop : IsCoprime fn fd) (u : k) (α : k)
    (hΦ : Phi k fn fd u ≠ 0) (hα : α ∈ (Phi k fn fd u).roots) :
    Polynomial.aeval α fd ≠ 0 ∧ Polynomial.aeval α fn / Polynomial.aeval α fd = u := by
  rw [Polynomial.mem_roots hΦ, Polynomial.IsRoot, Phi, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
    sub_eq_zero] at hα
  have hfd : Polynomial.aeval α fd ≠ 0 := by
    intro h0
    have hfn : Polynomial.aeval α fn = 0 := by rw [hα, h0, mul_zero]
    obtain ⟨a, b, hab⟩ := hcop
    have := congrArg (Polynomial.aeval α) hab
    simp only [map_add, map_mul, hfn, h0, mul_zero, add_zero, map_one] at this
    exact zero_ne_one this
  exact ⟨hfd, by rw [div_eq_iff hfd, hα]⟩

end Pencil

section Loc

theorem exists_clear_denom (D : ℕ) (ℓ : F[X]) (σ : Fin D → F[X])
    (q : MvPolynomial (Fin D) F) :
    ∃ (a : F[X]) (n : ℕ), ∀ u : k, Polynomial.aeval u ℓ ≠ 0 →
      MvPolynomial.aeval (fun i => Polynomial.aeval u (σ i) / Polynomial.aeval u ℓ) q *
        Polynomial.aeval u ℓ ^ n = Polynomial.aeval u a := by
  classical
  let A := Localization.Away ℓ
  let s : Fin D → A := fun i => algebraMap F[X] A (σ i) * IsLocalization.Away.invSelf ℓ
  let r : A := MvPolynomial.eval₂Hom ((algebraMap F[X] A).comp Polynomial.C) s q
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers ℓ) r
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp b.2
  refine ⟨a, n, fun u hu => ?_⟩

  have hunit : IsUnit ((Polynomial.aeval u : F[X] →ₐ[F] k).toRingHom ℓ) :=
    isUnit_iff_ne_zero.mpr hu
  let ev : A →+* k := IsLocalization.Away.lift ℓ hunit
  have hev_alg : ∀ x : F[X], ev (algebraMap F[X] A x) = Polynomial.aeval u x := fun x =>
    IsLocalization.Away.lift_eq ℓ hunit x
  have hev_inv : ev (IsLocalization.Away.invSelf ℓ) = (Polynomial.aeval u ℓ)⁻¹ := by
    have h1 := congrArg ev (IsLocalization.Away.mul_invSelf ℓ (S := A))
    rw [map_mul, map_one, hev_alg] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hev_r : ev r =
      MvPolynomial.aeval (fun i => Polynomial.aeval u (σ i) / Polynomial.aeval u ℓ) q := by
    have hc := MvPolynomial.comp_eval₂Hom ((algebraMap F[X] A).comp Polynomial.C) s ev
    have hc' := DFunLike.congr_fun hc q
    simp only [RingHom.comp_apply] at hc'
    change ev r = _
    have hring : ev.comp ((algebraMap F[X] A).comp Polynomial.C) = algebraMap F k := by
      refine RingHom.ext fun c => ?_
      simp only [RingHom.comp_apply, hev_alg, Polynomial.aeval_C]
    have hfun : (fun i => ev (s i)) =
        fun i => Polynomial.aeval u (σ i) / Polynomial.aeval u ℓ := by
      funext i
      simp only [s, map_mul, hev_alg, hev_inv, div_eq_mul_inv]
    rw [hc', hring, hfun, MvPolynomial.aeval_def, MvPolynomial.coe_eval₂Hom]
  have := congrArg ev hab
  simp only [map_mul] at this
  rw [hev_r, hev_alg, ← hn, hev_alg, map_pow] at this
  exact this

end Loc

section Frob

theorem coeff_X_sub_C_pow_self (c : k) (D : ℕ) :
    ((Polynomial.X - Polynomial.C c) ^ D).coeff D = 1 := by
  have : (Polynomial.X : k[X]) - Polynomial.C c = Polynomial.X + Polynomial.C (-c) := by
    rw [map_neg, sub_eq_add_neg]
  rw [this, Polynomial.coeff_X_add_C_pow]
  simp

theorem coeff_X_sub_C_pow_frob (p : ℕ) [ExpChar k p] (c : k) (s D' : ℕ) (hD' : 1 ≤ D') :
    ((Polynomial.X - Polynomial.C c) ^ (p ^ s * D')).coeff ((D' - 1) * p ^ s) =
      -(D' : k) * c ^ p ^ s := by
  have hp : 0 < p ^ s := pow_pos (expChar_pos k p) s
  have h1 : ((Polynomial.X : k[X]) - Polynomial.C c) ^ (p ^ s * D') =
      Polynomial.expand k (p ^ s) ((Polynomial.X - Polynomial.C (c ^ p ^ s)) ^ D') := by
    rw [pow_mul, sub_pow_expChar_pow (Polynomial.X : k[X]) (Polynomial.C c) s (p := p),
      map_pow, map_sub, Polynomial.expand_X, Polynomial.expand_C, ← Polynomial.C_pow]
  rw [h1, Polynomial.coeff_expand_mul hp]
  have : (Polynomial.X : k[X]) - Polynomial.C (c ^ p ^ s) =
      Polynomial.X + Polynomial.C (-(c ^ p ^ s)) := by
    rw [map_neg, sub_eq_add_neg]
  rw [this, Polynomial.coeff_X_add_C_pow, Nat.sub_sub_self hD', Nat.choose_symm hD',
    Nat.choose_one_right]
  ring

variable (F k) in

theorem exists_pow_mul_of_expChar (p : ℕ) [ExpChar F p] (D : ℕ) (hD : D ≠ 0) :
    ∃ s D' : ℕ, D = p ^ s * D' ∧ (D' : k) ≠ 0 := by
  rcases expChar_is_prime_or_one F p with hp | hp
  · haveI : CharP F p := by
      cases ‹ExpChar F p› with
      | zero => exact absurd hp Nat.not_prime_one
      | prime hprime => assumption
    haveI : CharP k p := charP_of_injective_algebraMap (algebraMap F k).injective p
    obtain ⟨s, D', hndvd, hDeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD p hp.ne_one
    refine ⟨s, D', hDeq, ?_⟩
    intro h0
    exact hndvd ((CharP.cast_eq_zero_iff k p D').mp h0)
  · subst hp
    haveI : CharZero F := by
      cases ‹ExpChar F 1› with
      | zero => assumption
      | prime hprime => exact absurd hprime Nat.not_prime_one
    haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap F k).injective
    refine ⟨0, D, by simp, ?_⟩
    exact_mod_cast hD

end Frob

theorem core [IsAlgClosed k] (fn fd gn gd : F[X]) (hcop : IsCoprime fn fd) (hfd0 : fd ≠ 0)
    (hf : ∀ c : F, fn ≠ Polynomial.C c * fd)
    (m : k → k) (S : Set k) (hS : S.Finite)
    (H : ∀ x : k, x ∉ S → Polynomial.aeval x fd ≠ 0 ∧ Polynomial.aeval x gd ≠ 0 ∧
      m (Polynomial.aeval x fn / Polynomial.aeval x fd) =
        Polynomial.aeval x gn / Polynomial.aeval x gd) :
    ∃ (t : ℕ) (hn hd : F[X]) (T : Set k), T.Finite ∧ ∀ u : k, u ∉ T →
      Polynomial.aeval u hd ≠ 0 ∧
        m u ^ ringExpChar F ^ t = Polynomial.aeval u hn / Polynomial.aeval u hd := by
  classical

  set D : ℕ := max fn.natDegree fd.natDegree with hDdef
  have hnD : fn.natDegree ≤ D := le_max_left _ _
  have hdD : fd.natDegree ≤ D := le_max_right _ _
  have hD0 : D ≠ 0 := by
    intro hD
    have h1 : fn.natDegree = 0 := Nat.eq_zero_of_le_zero (hD ▸ hnD)
    have h2 : fd.natDegree = 0 := Nat.eq_zero_of_le_zero (hD ▸ hdD)
    rw [Polynomial.natDegree_eq_zero] at h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have hb0 : b ≠ 0 := by rintro rfl; exact hfd0 (by rw [← hb, map_zero])
    apply hf (a / b)
    rw [← ha, ← hb, ← map_mul, div_mul_cancel₀ a hb0]

  set ℓ : F[X] := ell D fn fd with hℓdef
  have hℓ0 : ℓ ≠ 0 := by
    intro h0
    have hc0 : ℓ.coeff 0 = 0 := by rw [h0, Polynomial.coeff_zero]
    have hc1 : ℓ.coeff 1 = 0 := by rw [h0, Polynomial.coeff_zero]
    simp only [hℓdef, ell, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
      Polynomial.coeff_X_mul_zero, sub_zero] at hc0
    simp only [hℓdef, ell, Polynomial.coeff_sub, Polynomial.coeff_C_succ,
      Polynomial.coeff_X_mul, Polynomial.coeff_C_zero, zero_sub, neg_eq_zero] at hc1

    rcases eq_or_ne fd.natDegree D with h | h
    · apply hfd0
      apply Polynomial.leadingCoeff_eq_zero.mp
      rw [Polynomial.leadingCoeff, h]; exact hc1
    · have hfn : fn.natDegree = D := by
        rcases max_choice fn.natDegree fd.natDegree with h' | h'
        · exact h'.symm
        · exact absurd h'.symm h
      have hfn0 : fn ≠ 0 := by
        rintro rfl
        simp only [Polynomial.natDegree_zero] at hfn
        exact hD0 hfn.symm
      apply hfn0
      apply Polynomial.leadingCoeff_eq_zero.mp
      rw [Polynomial.leadingCoeff, hfn]; exact hc0

  set T₁ : Set k := (fun s => Polynomial.aeval s fn / Polynomial.aeval s fd) '' S with hT₁
  set T₂ : Set k := {u | Polynomial.aeval u ℓ = 0} with hT₂
  have hT₁fin : T₁.Finite := hS.image _
  have hT₂fin : T₂.Finite := by
    have hne : ℓ.map (algebraMap F k) ≠ 0 := Polynomial.map_ne_zero hℓ0
    have := Polynomial.finite_setOf_isRoot hne
    refine this.subset ?_
    intro u hu
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact hu

  have hq : ∀ j : ℕ, ∃ (a : F[X]) (n : ℕ), ∀ (u : k), Polynomial.aeval u ℓ ≠ 0 →
      ∀ α : Fin D → k, Finset.univ.val.map α = (Phi k fn fd u).roots →
        MvPolynomial.aeval α ((E F D gn gd).coeff j) * Polynomial.aeval u ℓ ^ n =
          Polynomial.aeval u a := by
    intro j
    obtain ⟨q, hq⟩ := exists_q (F := F) D gn gd j
    obtain ⟨a, n, han⟩ := exists_clear_denom (k := k) D ℓ (sig D fn fd) q
    refine ⟨a, n, fun u hu α hα => ?_⟩
    rw [← hq, aeval_q, hα]
    have : (fun i : Fin D => (Phi k fn fd u).roots.esymm ((i : ℕ) + 1)) =
        fun i => Polynomial.aeval u (sig D fn fd i) / Polynomial.aeval u ℓ := by
      funext i
      exact esymm_roots_Phi fn fd u D hnD hdD hu i
    rw [this]
    exact han u hu
  choose a n han using hq

  obtain ⟨p, hpF⟩ := ExpChar.exists F
  have hpeq : ringExpChar F = p := ringExpChar.eq F p
  haveI : ExpChar k p := expChar_of_injective_algebraMap (algebraMap F k).injective p
  obtain ⟨s, D', hDeq, hD'⟩ := exists_pow_mul_of_expChar F k p D hD0
  have hD'1 : 1 ≤ D' := by
    rcases Nat.eq_zero_or_pos D' with h | h
    · exact absurd (by rw [hDeq, h, mul_zero]) hD0
    · exact h
  set j₀ : ℕ := (D' - 1) * p ^ s with hj₀

  refine ⟨s, -(a j₀ * ℓ ^ n D), Polynomial.C (D' : F) * ℓ ^ n j₀ * a D, T₁ ∪ T₂,
    hT₁fin.union hT₂fin, fun u hu => ?_⟩
  rw [Set.mem_union, not_or] at hu
  obtain ⟨hu₁, hu₂⟩ := hu
  have hℓu : Polynomial.aeval u ℓ ≠ 0 := hu₂

  have hΦ0 : Phi k fn fd u ≠ 0 := Phi_ne_zero fn fd u D hℓu
  have hcard : (Phi k fn fd u).roots.card = D := by
    rw [IsAlgClosed.card_roots_eq_natDegree (p := Phi k fn fd u), Phi_natDegree_eq fn fd u D hnD hdD hℓu]
  set α : Fin D → k := enum (Phi k fn fd u).roots with hαdef
  have hα : Finset.univ.val.map α = (Phi k fn fd u).roots := enum_spec _ hcard
  have hgood : ∀ i, Polynomial.aeval (α i) gd ≠ 0 ∧
      Polynomial.aeval (α i) gn / Polynomial.aeval (α i) gd = m u := by
    intro i
    have hmem : α i ∈ (Phi k fn fd u).roots := enum_mem _ hcard i
    obtain ⟨hfdα, hfα⟩ := root_Phi fn fd hcop u (α i) hΦ0 hmem
    have hαS : α i ∉ S := by
      intro hS'
      apply hu₁
      exact ⟨α i, hS', hfα⟩
    obtain ⟨-, hgd, hm⟩ := H (α i) hαS
    rw [hfα] at hm
    exact ⟨hgd, hm.symm⟩
  set N : k := ∏ i, Polynomial.aeval (α i) gd with hNdef
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hgood i).1

  have hidD := han D u hℓu α hα
  have hidj := han j₀ u hℓu α hα
  rw [aeval_E_coeff_of_const D gn gd α (m u) hgood] at hidD hidj
  rw [coeff_X_sub_C_pow_self, mul_one] at hidD
  have hcoef : ((Polynomial.X - Polynomial.C (m u)) ^ D).coeff j₀ =
      -(D' : k) * m u ^ p ^ s := by
    rw [hDeq, hj₀]
    exact coeff_X_sub_C_pow_frob p (m u) s D' hD'1
  rw [hcoef] at hidj

  have haD : Polynomial.aeval u (a D) ≠ 0 := by
    rw [← hidD]; exact mul_ne_zero hN0 (pow_ne_zero _ hℓu)
  have hden : Polynomial.aeval u (Polynomial.C (D' : F) * ℓ ^ n j₀ * a D) ≠ 0 := by
    simp only [map_mul, map_pow, map_natCast]
    exact mul_ne_zero (mul_ne_zero hD' (pow_ne_zero _ hℓu)) haD
  refine ⟨hden, ?_⟩
  rw [hpeq, eq_div_iff hden]
  simp only [map_mul, map_pow, map_neg, map_natCast]
  rw [← hidD, ← hidj]
  ring

end PolyFrobDescent

theorem solution
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k]
    (fn fd gn gd : Polynomial F) (hf : ∀ c : F, fn ≠ Polynomial.C c * fd)
    (m : k → k) (S : Set k) (hS : S.Finite)
    (H : ∀ x : k, x ∉ S → Polynomial.aeval x fd ≠ 0 ∧ Polynomial.aeval x gd ≠ 0 ∧
      m (Polynomial.aeval x fn / Polynomial.aeval x fd) =
        Polynomial.aeval x gn / Polynomial.aeval x gd) :
    ∃ (t : ℕ) (hn hd : Polynomial F) (T : Set k), T.Finite ∧ ∀ u : k, u ∉ T →
      Polynomial.aeval u hd ≠ 0 ∧
        m u ^ ringExpChar F ^ t = Polynomial.aeval u hn / Polynomial.aeval u hd := by
  classical

  rcases eq_or_ne fd 0 with hfd0 | hfd0
  · exfalso
    obtain ⟨x, -, hx⟩ := ((Set.infinite_univ (α := k)).diff hS).nonempty
    exact (H x hx).1 (by rw [hfd0, map_zero])

  set G : F[X] := EuclideanDomain.gcd fn fd with hG
  have hGfd : G ∣ fd := EuclideanDomain.gcd_dvd_right fn fd
  have hGfn : G ∣ fn := EuclideanDomain.gcd_dvd_left fn fd
  have hG0 : G ≠ 0 := fun h => hfd0 (zero_dvd_iff.mp (h ▸ hGfd))
  obtain ⟨fn', hfn'⟩ := hGfn
  obtain ⟨fd', hfd'⟩ := hGfd
  have hcop : IsCoprime fn' fd' := by
    set ca : F[X] := EuclideanDomain.gcdA fn fd with hca
    set cb : F[X] := EuclideanDomain.gcdB fn fd with hcb
    have hbez : G = fn * ca + fd * cb := EuclideanDomain.gcd_eq_gcd_ab fn fd
    clear_value ca cb
    rw [hfn', hfd'] at hbez
    refine ⟨ca, cb, ?_⟩
    apply mul_left_cancel₀ hG0
    calc G * (ca * fn' + cb * fd') = G * fn' * ca + G * fd' * cb := by ring
      _ = G := hbez.symm
      _ = G * 1 := (mul_one G).symm
  have hfd'0 : fd' ≠ 0 := by rintro rfl; exact hfd0 (by rw [hfd', mul_zero])
  have hf' : ∀ c : F, fn' ≠ Polynomial.C c * fd' := by
    intro c hc
    apply hf c
    rw [hfn', hfd', hc]; ring
  have H' : ∀ x : k, x ∉ S → Polynomial.aeval x fd' ≠ 0 ∧ Polynomial.aeval x gd ≠ 0 ∧
      m (Polynomial.aeval x fn' / Polynomial.aeval x fd') =
        Polynomial.aeval x gn / Polynomial.aeval x gd := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := H x hx
    rw [hfd', map_mul] at h1
    have hGx : Polynomial.aeval x G ≠ 0 := left_ne_zero_of_mul h1
    have hfd'x : Polynomial.aeval x fd' ≠ 0 := right_ne_zero_of_mul h1
    refine ⟨hfd'x, h2, ?_⟩
    rw [← h3, hfn', hfd', map_mul, map_mul, mul_div_mul_left _ _ hGx]
  exact PolyFrobDescent.core fn' fd' gn gd hcop hfd'0 hf' m S hS H'

end S_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
end P2MW
export P2MW.S_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational (solution)
