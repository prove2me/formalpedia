-- Prove2me | solution 1 for Submodule.span_fixedPoints_eq_top_of_frobenius_semilinear_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8728c742-49ca-5153-a79f-10bc8e3a7bab

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective

set_option autoImplicit false

open Polynomial

namespace LangSteinbergSol

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section General

variable (q : ℕ) (θ : V →+ V) (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ q • θ v)
include hθ

theorem map_sum_smul {ι : Type*} (s : Finset ι) (c : ι → K) (w : ι → V) :
    θ (∑ i ∈ s, c i • w i) = ∑ i ∈ s, c i ^ q • θ (w i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => hθ (c i) (w i)

theorem natCard_le_pow_finrank_span (hq : 1 < q) (Y : Set V) (hYfin : Y.Finite)
    (hY : ∀ y ∈ Y, θ y = y) :
    Nat.card Y ≤ q ^ Module.finrank K (Submodule.span K Y) := by
  classical

  obtain ⟨b, hbY, hbspan, hbli⟩ := exists_linearIndependent K Y
  have hbfin : b.Finite := hYfin.subset hbY
  haveI : Fintype b := hbfin.fintype
  haveI : Fintype Y := hYfin.fintype

  set S : Set K := {c : K | c ^ q = c} with hSdef
  have hne : (X ^ q - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hSsub : S ⊆ ((X ^ q - X : K[X]).roots.toFinset : Set K) := by
    intro c hc
    have hc' : c ^ q = c := hc
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub,
      eval_pow, eval_X, hc', sub_self]
  have hSfin : S.Finite := Set.Finite.subset (Finset.finite_toSet _) hSsub
  haveI : Fintype S := hSfin.fintype
  have hScard : Fintype.card S ≤ q := by
    have h1 : Fintype.card S ≤ ((X ^ q - X : K[X]).roots.toFinset).card := by
      rw [← Set.toFinset_card]
      exact Finset.card_le_card (by simpa using hSsub)
    refine h1.trans ((Multiset.toFinset_card_le _).trans ?_)
    have := card_roots' (X ^ q - X : K[X])
    rwa [FiniteField.X_pow_card_sub_X_natDegree_eq K hq] at this

  have hrepr : ∀ y : Y, ∃ l : b → S, ∑ x : b, ((l x : K)) • (x : V) = y := by
    rintro ⟨y, hy⟩
    have hyspan : y ∈ Submodule.span K (Set.range ((↑) : b → V)) := by
      rw [Subtype.range_coe, hbspan]
      exact Submodule.subset_span hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hyspan
    have hθy : θ y = y := hY y hy
    have h1 : ∑ x : b, (c x ^ q) • (x : V) = y := by
      have h := map_sum_smul q θ hθ Finset.univ c (fun x : b => (x : V))
      rw [hc, hθy] at h
      rw [h]
      exact Finset.sum_congr rfl fun x _ => by rw [hY x (hbY x.2)]
    have hdiff : ∑ x : b, (c x ^ q - c x) • (x : V) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1, hc, sub_self]
    have hcoef : ∀ x : b, c x ^ q - c x = 0 :=
      Fintype.linearIndependent_iff.mp hbli (fun x => c x ^ q - c x) hdiff
    refine ⟨fun x => ⟨c x, ?_⟩, ?_⟩
    · show c x ^ q = c x
      exact sub_eq_zero.mp (hcoef x)
    · exact hc
  choose l hl using hrepr
  have hlinj : Function.Injective l := by
    intro y₁ y₂ h
    apply Subtype.ext
    rw [← hl y₁, ← hl y₂, h]

  have hcard : Nat.card Y ≤ Fintype.card S ^ Fintype.card b := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_fun]
    exact Fintype.card_le_of_injective l hlinj
  have hrank : Module.finrank K (Submodule.span K Y) = Fintype.card b := by
    rw [← hbspan, finrank_span_set_eq_card hbli, Set.toFinset_card]
  rw [hrank]
  exact hcard.trans (Nat.pow_le_pow_left hScard _)

end General

end LangSteinbergSol

namespace LangSteinbergSol

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_mem_span_lt_of_sum_eq_zero {n : ℕ} (g : Fin n → K) (w : Fin n → V)
    (h : ∑ i, g i • w i = 0) (hg : ∃ i, g i ≠ 0) :
    ∃ j : Fin n, g j ≠ 0 ∧ w j ∈ Submodule.span K (w '' {i | i < j}) := by
  classical
  set T : Finset (Fin n) := Finset.univ.filter fun i => g i ≠ 0 with hT
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, by simp [hT, hi]⟩
  set j := T.max' hTne with hj
  have hjT : j ∈ T := Finset.max'_mem T hTne
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hjT).2
  have hle : ∀ i, g i ≠ 0 → i ≤ j := fun i hi => Finset.le_max' T i (by simp [hT, hi])
  refine ⟨j, hgj, ?_⟩
  have hsplit := Finset.add_sum_erase Finset.univ (fun i => g i • w i) (Finset.mem_univ j)
  rw [h] at hsplit
  have hwj : w j = -(g j)⁻¹ • ∑ i ∈ Finset.univ.erase j, g i • w i := by
    have : g j • w j = -∑ i ∈ Finset.univ.erase j, g i • w i := eq_neg_of_add_eq_zero_left hsplit
    calc w j = (g j)⁻¹ • (g j • w j) := by rw [smul_smul, inv_mul_cancel₀ hgj, one_smul]
      _ = _ := by rw [this, smul_neg, neg_smul]
  rw [hwj]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => ?_)
  rcases eq_or_ne (g i) 0 with h0 | h0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_, rfl⟩)
    exact lt_of_le_of_ne (hle i h0) (Finset.ne_of_mem_erase hi)

section Kap

noncomputable def kap (q : ℕ) (a : ℕ → K) : ℕ → K[X]
  | 0 => C (a 0) * X ^ q
  | i + 1 => kap q a i ^ q + C (a (i + 1)) * X ^ q

theorem kap_zero (q : ℕ) (a : ℕ → K) : kap q a 0 = C (a 0) * X ^ q := rfl

theorem kap_succ (q : ℕ) (a : ℕ → K) (i : ℕ) :
    kap q a (i + 1) = kap q a i ^ q + C (a (i + 1)) * X ^ q := rfl

theorem eval_kap_succ (q : ℕ) (a : ℕ → K) (i : ℕ) (c : K) :
    (kap q a (i + 1)).eval c = ((kap q a i).eval c) ^ q + a (i + 1) * c ^ q := by
  rw [kap_succ, eval_add, eval_pow, eval_mul, eval_C, eval_pow, eval_X]

theorem eval_kap_zero (q : ℕ) (a : ℕ → K) (c : K) : (kap q a 0).eval c = a 0 * c ^ q := by
  rw [kap_zero, eval_mul, eval_C, eval_pow, eval_X]

variable {p : ℕ}

theorem derivative_kap [CharP K p] (s : ℕ) (hs : s ≠ 0) (a : ℕ → K) (i : ℕ) :
    derivative (kap (p ^ s) a i) = 0 := by
  have hq0 : ((p ^ s : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero K p, zero_pow hs]
  have hCX : ∀ b : K, derivative (C b * X ^ p ^ s) = 0 := by
    intro b
    rw [derivative_C_mul_X_pow, hq0, mul_zero, C_0, zero_mul]
  induction i with
  | zero => rw [kap_zero, hCX]
  | succ i ih => rw [kap_succ, derivative_add, derivative_pow, ih, mul_zero, zero_add, hCX]

theorem natDegree_kap [Fact p.Prime] (s : ℕ) (hs : s ≠ 0) (a : ℕ → K) (ha : a 0 ≠ 0) (i : ℕ) :
    (kap (p ^ s) a i).natDegree = (p ^ s) ^ (i + 1) ∧ kap (p ^ s) a i ≠ 0 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : 1 < p ^ s := Nat.one_lt_pow hs hp
  induction i with
  | zero =>
    refine ⟨by rw [kap_zero, natDegree_C_mul_X_pow _ _ ha, zero_add, pow_one], ?_⟩
    rw [kap_zero]
    exact mul_ne_zero (C_ne_zero.mpr ha) (pow_ne_zero _ X_ne_zero)
  | succ i ih =>
    obtain ⟨ihdeg, ihne⟩ := ih
    have hdegpow : (kap (p ^ s) a i ^ p ^ s).natDegree = (p ^ s) ^ (i + 2) := by
      rw [natDegree_pow, ihdeg]; ring
    have hlt : (C (a (i + 1)) * X ^ p ^ s).natDegree < (kap (p ^ s) a i ^ p ^ s).natDegree := by
      rw [hdegpow]
      refine lt_of_le_of_lt (natDegree_C_mul_X_pow_le _ _) ?_
      calc p ^ s = (p ^ s) ^ 1 := (pow_one _).symm
        _ < (p ^ s) ^ (i + 2) := Nat.pow_lt_pow_right hq (by omega)
    have hdeg : (kap (p ^ s) a (i + 1)).natDegree = (p ^ s) ^ (i + 2) := by
      rw [kap_succ, natDegree_add_eq_left_of_natDegree_lt hlt, hdegpow]
    refine ⟨hdeg, fun h => ?_⟩
    have := congrArg natDegree h
    rw [hdeg, natDegree_zero] at this
    exact pow_ne_zero _ (by omega) this

end Kap

section Main

variable [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem span_fixedPoints_eq_top [FiniteDimensional K V] (s : ℕ) (hs : s ≠ 0) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v) (hinj : Function.Injective θ) :
    Submodule.span K (Function.fixedPoints θ) = ⊤ := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set q : ℕ := p ^ s with hqdef
  have hq : 1 < q := Nat.one_lt_pow hs hp
  have hq0 : q ≠ 0 := by omega
  haveI : ExpChar K p := ExpChar.prime Fact.out
  haveI : PerfectRing K p := PerfectField.toPerfectRing p

  set ρ : K → K := fun c => (iterateFrobeniusEquiv K p s).symm c with hρdef
  have hρ : ∀ c : K, ρ c ^ q = c := fun c => by
    rw [hqdef, ← iterateFrobeniusEquiv_def K p s]
    exact (iterateFrobeniusEquiv K p s).apply_symm_apply c
  rw [eq_top_iff]
  rintro v -
  rcases eq_or_ne v 0 with rfl | hv
  · exact Submodule.zero_mem _

  set f : ℕ → V := fun i => (⇑θ)^[i] v with hfdef
  have hf0 : f 0 = v := rfl
  have hfsucc : ∀ i, f (i + 1) = θ (f i) := fun i => Function.iterate_succ_apply' θ i v
  have hfne : ∀ i, f i ≠ 0 := by
    intro i
    induction i with
    | zero => exact hv
    | succ i ih =>
      rw [hfsucc]
      intro h
      exact ih (hinj (h.trans (map_zero θ).symm))

  have hex : ∃ m : ℕ, f m ∈ Submodule.span K (f '' Set.Iio m) := by
    set n := Module.finrank K V
    have hnot : ¬ LinearIndependent K (fun i : Fin (n + 1) => f i) := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_fin] at this
      omega
    obtain ⟨g, hg, hgi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    obtain ⟨j, -, hj⟩ := exists_mem_span_lt_of_sum_eq_zero g (fun i : Fin (n + 1) => f i) hg hgi
    refine ⟨j, Submodule.span_mono ?_ hj⟩
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  set m := Nat.find hex with hmdef
  have hm : f m ∈ Submodule.span K (f '' Set.Iio m) := Nat.find_spec hex
  have hmin : ∀ j < m, f j ∉ Submodule.span K (f '' Set.Iio j) := fun j hj => Nat.find_min hex hj
  have hm0 : m ≠ 0 := by
    intro h0
    have := hm
    rw [h0] at this
    have hemp : f '' Set.Iio 0 = ∅ := by
      ext w
      simp
    rw [hemp, Submodule.span_empty, Submodule.mem_bot] at this
    exact hfne 0 this
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  clear_value m
  subst hm'

  set e : Fin (m' + 1) → V := fun i => f i with hedef
  have hrange : f '' Set.Iio (m' + 1) = Set.range e := by
    ext w
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
  have hli : LinearIndependent K e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨j, -, hj⟩ := exists_mem_span_lt_of_sum_eq_zero g e hg hne
    refine hmin j j.2 (Submodule.span_mono ?_ hj)
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

  rw [hrange] at hm
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm

  have ha0 : a 0 ≠ 0 := by
    intro ha0

    set u : V := ∑ i : Fin m', ρ (a i.succ) • f i with hudef
    have hθu : θ u = f (m' + 1) := by
      rw [hudef, map_sum_smul q θ hθ, ← ha, Fin.sum_univ_succ, ha0, zero_smul, zero_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hρ, hedef]
      simp only [Fin.val_succ]
      rw [hfsucc]
    have hum : f m' = u := hinj (by rw [hθu, hfsucc])
    refine hmin m' (by omega) ?_
    rw [hum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨i, i.2, rfl⟩

  set a' : ℕ → K := fun i => if h : i < m' + 1 then a ⟨i, h⟩ else 0 with ha'def
  have ha' : ∀ i : Fin (m' + 1), a' i = a i := fun i => by
    show (if h : (i : ℕ) < m' + 1 then a ⟨i, h⟩ else 0) = a i
    rw [dif_pos i.2]
  have ha'0 : a' 0 ≠ 0 := by
    have h := ha' 0
    simp only [Fin.val_zero] at h
    rwa [h]
  have ha'0' : a' 0 = a 0 := by
    have h := ha' 0
    simpa only [Fin.val_zero] using h
  have ha'succ : ∀ i : Fin m', a' ((i : ℕ) + 1) = a i.succ := fun i => by
    have h := ha' i.succ
    simpa only [Fin.val_succ] using h
  set ev : ℕ → K → K := fun i c => (kap q a' i).eval c with hevdef
  have hev0 : ∀ c, ev 0 c = a 0 * c ^ q := fun c => by
    show (kap q a' 0).eval c = a 0 * c ^ q
    rw [eval_kap_zero, ha'0']
  have hevsucc : ∀ (i : ℕ) (c : K), ev (i + 1) c = ev i c ^ q + a' (i + 1) * c ^ q := fun i c =>
    eval_kap_succ q a' i c
  set x : K → V := fun c => ∑ i : Fin (m' + 1), ev i c • f i with hxdef
  have hxc' : ∀ c, x c = ∑ i : Fin (m' + 1), ev i c • f i := fun c => rfl
  have hfm : f (m' + 1) = a 0 • f 0 + ∑ i : Fin m', a i.succ • f ((i : ℕ) + 1) := by
    rw [← ha, Fin.sum_univ_succ]
    simp only [hedef, Fin.val_zero, Fin.val_succ]

  have hkey : ∀ c : K, θ (x c) - x c = (ev m' c - c) ^ q • f (m' + 1) := by
    intro c
    have hθx : θ (x c) = (∑ i : Fin m', ev i c ^ q • f (i + 1)) + ev m' c ^ q • f (m' + 1) := by
      rw [hxc', map_sum_smul q θ hθ, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ← hfsucc]
    have hsum' : ∑ i : Fin m', (a' ((i : ℕ) + 1) * c ^ q) • f ((i : ℕ) + 1)
        = ∑ i : Fin m', (c ^ q * a i.succ) • f ((i : ℕ) + 1) :=
      Finset.sum_congr rfl fun i _ => by rw [ha'succ i, mul_comm]
    have hxc : x c = c ^ q • f (m' + 1) + ∑ i : Fin m', ev i c ^ q • f (i + 1) := by
      rw [hxc', Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, hev0, hevsucc, add_smul, Finset.sum_add_distrib,
        hsum', hfm, smul_add, Finset.smul_sum, smul_smul, mul_comm (c ^ q) (a 0)]
      abel
    rw [hθx, hxc, sub_pow_char_pow, sub_smul]
    abel

  set H : K[X] := kap q a' m' - X with hHdef
  have hroot : ∀ c : K, H.IsRoot c → θ (x c) = x c := by
    intro c hc
    have hc' : ev m' c = c := by
      rw [IsRoot.def, hHdef, eval_sub, eval_X] at hc
      exact sub_eq_zero.mp hc
    have := hkey c
    rw [hc', sub_self, zero_pow hq0, zero_smul] at this
    exact sub_eq_zero.mp this

  obtain ⟨hdegk, hkne⟩ := natDegree_kap (K := K) (p := p) s hs a' ha'0 m'
  have hdegH : H.natDegree = q ^ (m' + 1) := by
    rw [hHdef, natDegree_sub_eq_left_of_natDegree_lt, hdegk]
    rw [hdegk, natDegree_X]
    calc 1 < q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (m' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsep : H.Separable := by
    rw [separable_def, hHdef, derivative_sub, derivative_kap s hs, derivative_X, zero_sub]
    exact isCoprime_one_right.neg_right
  have hcardroots : H.roots.toFinset.card = q ^ (m' + 1) := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      hdegH]

  have hxinj : Set.InjOn x (H.roots.toFinset : Set K) := by
    intro c₁ hc₁ hc₂' hc₂ hxx
    have hH0 : H ≠ 0 := by
      intro h; rw [h, natDegree_zero] at hdegH; exact pow_ne_zero _ hq0 hdegH.symm
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hH0] at hc₁ hc₂
    have hcoef : ∀ i : Fin (m' + 1), ev i c₁ - ev i hc₂' = 0 := by
      refine Fintype.linearIndependent_iff.mp hli (fun i => ev i c₁ - ev i hc₂') ?_
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hxx
    have h1 : ev m' c₁ = c₁ := by
      have := hc₁; rw [IsRoot.def, hHdef, eval_sub, eval_X] at this; exact sub_eq_zero.mp this
    have h2 : ev m' hc₂' = hc₂' := by
      have := hc₂; rw [IsRoot.def, hHdef, eval_sub, eval_X] at this; exact sub_eq_zero.mp this
    have := hcoef (Fin.last m')
    simp only [Fin.val_last] at this
    rw [← h1, ← h2]
    exact sub_eq_zero.mp this

  set Y : Finset V := H.roots.toFinset.image x with hYdef
  have hYcard : Y.card = q ^ (m' + 1) := by
    rw [hYdef, Finset.card_image_of_injOn hxinj, hcardroots]
  have hYfix : ∀ y ∈ (Y : Set V), θ y = y := by
    intro y hy
    rw [Finset.mem_coe, hYdef, Finset.mem_image] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hH0 : H ≠ 0 := by
      intro h; rw [h, natDegree_zero] at hdegH; exact pow_ne_zero _ hq0 hdegH.symm
    exact hroot c ((mem_roots hH0).mp (Multiset.mem_toFinset.mp hc))

  set U : Submodule K V := Submodule.span K (Set.range e) with hUdef
  have hYU : Submodule.span K (Y : Set V) ≤ U := by
    rw [Submodule.span_le]
    intro y hy
    rw [Finset.mem_coe, hYdef, Finset.mem_image] at hy
    obtain ⟨c, -, rfl⟩ := hy
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hUrank : Module.finrank K U = m' + 1 := by
    rw [hUdef, finrank_span_eq_card hli, Fintype.card_fin]

  have hbound := natCard_le_pow_finrank_span q θ hθ hq (Y : Set V) Y.finite_toSet hYfix
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hYcard, Nat.pow_le_pow_iff_right hq] at hbound
  have hYeqU : Submodule.span K (Y : Set V) = U :=
    Submodule.eq_of_le_of_finrank_le hYU (by rw [hUrank]; exact hbound)

  have hvU : v ∈ U := Submodule.subset_span ⟨0, rfl⟩
  rw [← hYeqU] at hvU
  exact Submodule.span_mono (fun y hy => hYfix y hy) hvU

end Main

end LangSteinbergSol

theorem solution
    {K V : Type*} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (s : ℕ) (hs : s ≠ 0) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v) (hinj : Function.Injective θ) :
    Submodule.span K (Function.fixedPoints θ) = ⊤ :=
  LangSteinbergSol.span_fixedPoints_eq_top s hs θ hθ hinj

end S_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective
end P2MW
export P2MW.S_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective (solution)
