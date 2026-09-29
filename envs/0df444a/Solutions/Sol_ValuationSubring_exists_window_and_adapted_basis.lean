-- Prove2me | solution 1 for ValuationSubring.exists_window_and_adapted_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/eabca6ff-d3d6-5bc7-87f2-4f3de011aa22

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_window_and_adapted_basis

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace WindowAdaptedBasisSol

section Window

variable {L : Type*} [Field L] {ι : Type*} (O : Subring L) [IsNoetherianRing O] {r : ℕ}
  (x : Fin r → ι → L) (hO : ∀ i n, x i n ∈ O)

def colO (n : ι) : Fin r → O := fun i => ⟨x i n, hO i n⟩

include hO in
theorem exists_window :
    ∃ W : Finset ι, ∀ n : ι, ∃ c : W → O, ∀ i, x i n = ∑ m : W, (c m : L) * x i (m : ι) := by
  classical
  let β : ι → (Fin r → O) := colO O x hO
  let S : Submodule O (Fin r → O) := Submodule.span O (Set.range β)
  have hfg : S.FG := IsNoetherian.noetherian S
  have hcomp : IsCompactElement S := (Submodule.fg_iff_compact S).mp hfg
  have hle : S ≤ ⨆ n, Submodule.span O {β n} := by
    show Submodule.span O (Set.range β) ≤ _
    rw [Submodule.span_range_eq_iSup]
  obtain ⟨W, hW⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (hk := hcomp) (h := hle)
  refine ⟨W, fun n => ?_⟩
  have hn : β n ∈ ⨆ m ∈ W, Submodule.span O {β m} := hW (Submodule.subset_span ⟨n, rfl⟩)
  have heq : (⨆ m ∈ W, Submodule.span O {β m}) = Submodule.span O (Set.range fun m : W => β m) := by
    rw [Submodule.span_range_eq_iSup, iSup_subtype']
  rw [heq, Submodule.mem_span_range_iff_exists_fun] at hn
  obtain ⟨c, hc⟩ := hn
  refine ⟨c, fun i => ?_⟩
  have h := congrArg (fun v : Fin r → O => ((v i : O) : L)) hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  have hβ : ((β n i : O) : L) = x i n := rfl
  rw [← hβ, ← h]
  push_cast
  exact Finset.sum_congr rfl fun m _ => rfl

theorem window_property {W : Finset ι}
    (hW : ∀ n : ι, ∃ c : W → O, ∀ i, x i n = ∑ m : W, (c m : L) * x i (m : ι))
    (A : Subring L) (hOA : O ≤ A) (a : Fin r → L)
    (ha : ∀ n ∈ W, ∑ i, a i * x i n ∈ A) (n : ι) : ∑ i, a i * x i n ∈ A := by
  obtain ⟨c, hc⟩ := hW n
  have : ∑ i, a i * x i n = ∑ m : W, (c m : L) * ∑ i, a i * x i (m : ι) := by
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact A.sum_mem fun m _ => A.mul_mem (hOA (c m).2) (ha m m.2)

end Window

end WindowAdaptedBasisSol

namespace WindowAdaptedBasisSol

section Pivots

variable {L : Type*} [Field L] {ι : Type*} {r : ℕ}

theorem exists_pivots (x : Fin r → ι → L)
    (hx : ∀ a : Fin r → L, (∀ n, ∑ i, a i * x i n = 0) → ∀ i, a i = 0) :
    ∃ c : Fin r → ι, IsUnit (Matrix.of fun i k => x i (c k)) := by
  classical
  let col : ι → (Fin r → L) := fun n i => x i n

  have hspan : Submodule.span L (Set.range col) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hf0
    have ha : ∀ i, f (fun j => if i = j then 1 else 0) = 0 := by
      refine hx (fun i => f (fun j => if i = j then 1 else 0)) fun n => ?_
      have hn : f (col n) = 0 := hker (Submodule.subset_span ⟨n, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at hn
      have heq : ∑ i, (f fun j => if i = j then 1 else 0) * x i n
          = ∑ i, col n i • f fun j => if i = j then 1 else 0 :=
        Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
      rw [heq]; exact hn
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [ha i, smul_zero]
  obtain ⟨b, hb, hbspan, hbli⟩ := exists_linearIndependent L (Set.range col)
  rw [hspan] at hbspan
  have hbfin : b.Finite := hbli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = r := by
    have h1 := finrank_span_set_eq_card (R := L) (s := b) hbli
    rw [hbspan, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    rw [← Set.toFinset_card]; exact h1.symm
  let e : b ≃ Fin r := Fintype.equivFinOfCardEq hcard
  have hmem : ∀ k : Fin r, ((e.symm k : b) : Fin r → L) ∈ Set.range col := fun k => hb (e.symm k).2
  choose c hc using hmem
  refine ⟨c, ?_⟩
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have hcols : (Matrix.of fun i k => x i (c k)).col = fun k => ((e.symm k : b) : Fin r → L) := by
    funext k i
    rw [← hc k]
    rfl
  rw [hcols]
  exact hbli.comp _ e.symm.injective

end Pivots

section Gauss

variable {L : Type*} [Field L] (A : ValuationSubring L) {m : Type*} [Fintype m] [DecidableEq m]

theorem mem_cut_iff (U : Submodule L (m → L)) (n₀ : m) (w : m → L) :
    w ∈ (LinearMap.ker ((LinearMap.proj n₀ : (m → L) →ₗ[L] L).domRestrict U)).map U.subtype ↔
      w ∈ U ∧ w n₀ = 0 := by
  constructor
  · rintro ⟨⟨w, hwU⟩, hw, rfl⟩
    exact ⟨hwU, by simpa using hw⟩
  · rintro ⟨hwU, hw0⟩
    exact ⟨⟨w, hwU⟩, by simpa using hw0, rfl⟩

theorem gauss_elim : ∀ (r : ℕ) (U : Submodule L (m → L)), Module.finrank L U = r →
    ∃ (u : Fin r → m → L) (c : Fin r → m), (∀ k, u k ∈ U) ∧ (∀ k n, u k n ∈ A) ∧
      (∀ k l, u k (c l) = if k = l then 1 else 0) := by
  intro r
  induction r with
  | zero =>
    intro U hU
    exact ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun k => Fin.elim0 k,
      fun k => Fin.elim0 k⟩
  | succ r ih =>
    intro U hU

    have hUne : U ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hU
      exact Nat.succ_ne_zero r hU.symm
    obtain ⟨f, hfU, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    obtain ⟨n₁, hn₁⟩ : ∃ n, f n ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    haveI : Nonempty m := ⟨n₁⟩

    obtain ⟨n₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun n => A.valuation (f n))
      Finset.univ_nonempty
    have hfn₀ : f n₀ ≠ 0 := by
      intro h0
      have h1 := hmax n₁ (Finset.mem_univ _)
      rw [h0, map_zero] at h1
      exact hn₁ ((map_eq_zero A.valuation).mp (le_antisymm h1 zero_le'))
    set g : m → L := (f n₀)⁻¹ • f with hg
    have hgU : g ∈ U := U.smul_mem _ hfU
    have hgn₀ : g n₀ = 1 := by simp [hg, inv_mul_cancel₀ hfn₀]
    have hgA : ∀ n, g n ∈ A := by
      intro n
      rw [← A.valuation_le_one_iff]
      simp only [hg, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
      have hv0 : A.valuation (f n₀) ≠ 0 := (map_ne_zero A.valuation).mpr hfn₀
      rw [inv_mul_le_iff₀ (zero_lt_iff.mpr hv0), mul_one]
      exact hmax n (Finset.mem_univ n)

    set U' := (LinearMap.ker ((LinearMap.proj n₀ : (m → L) →ₗ[L] L).domRestrict U)).map U.subtype
      with hU'
    have hU'rank : Module.finrank L U' = r := by
      set φ := ((LinearMap.proj n₀ : (m → L) →ₗ[L] L).domRestrict U) with hφ
      have hsurj : LinearMap.range φ = ⊤ := by
        rw [eq_top_iff]
        rintro y -
        refine ⟨y • ⟨g, hgU⟩, ?_⟩
        simp [hφ, hgn₀]
      have h1 := LinearMap.finrank_range_add_finrank_ker φ
      rw [hsurj, finrank_top, Module.finrank_self, hU] at h1
      have h2 : Module.finrank L (LinearMap.ker φ) = r := by omega
      rw [hU', ← h2]
      exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ U.injective_subtype _).symm
    obtain ⟨u', c', hu'U, hu'A, hu'c⟩ := ih U' hU'rank
    have hu'mem : ∀ k, u' k ∈ U ∧ u' k n₀ = 0 := fun k => (mem_cut_iff U n₀ (u' k)).mp (hu'U k)

    refine ⟨Fin.cons (g - ∑ k, g (c' k) • u' k) u', Fin.cons n₀ c', ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_)
      · simp only [Fin.cons_zero]
        exact U.sub_mem hgU (U.sum_mem fun k _ => U.smul_mem _ (hu'mem k).1)
      · simp only [Fin.cons_succ]; exact (hu'mem k).1
    · refine Fin.cases (fun n => ?_) (fun k n => ?_)
      · simp only [Fin.cons_zero, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact sub_mem (hgA n) (sum_mem fun k _ => mul_mem (hgA _) (hu'A k n))
      · simp only [Fin.cons_succ]; exact hu'A k n
    · refine Fin.cases ?_ (fun k => ?_) <;> refine Fin.cases ?_ (fun l => ?_)
      · simp only [Fin.cons_zero, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          if_true]
        rw [hgn₀]
        have : ∑ k, g (c' k) * u' k n₀ = 0 :=
          Finset.sum_eq_zero fun k _ => by rw [(hu'mem k).2, mul_zero]
        rw [this, sub_zero]
      · simp only [Fin.cons_zero, Fin.cons_succ, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, if_neg (Fin.succ_ne_zero l).symm]
        simp_rw [hu'c]
        simp
      · simp only [Fin.cons_succ, Fin.cons_zero, if_neg (Fin.succ_ne_zero k)]
        exact (hu'mem k).2
      · simp only [Fin.cons_succ, hu'c, Fin.succ_inj]

end Gauss

end WindowAdaptedBasisSol

namespace WindowAdaptedBasisSol

section Assembly

variable {L : Type*} [Field L] {ι : Type*} (O : Subring L) [IsNoetherianRing O] {r : ℕ}

theorem main (x : Fin r → ι → L)
    (hx : ∀ a : Fin r → L, (∀ n, ∑ i, a i * x i n = 0) → ∀ i, a i = 0)
    (hO : ∀ i n, x i n ∈ O) :
    ∃ (W : Finset ι) (δ : L), δ ∈ O ∧ δ ≠ 0 ∧
      (∀ A : Subring L, O ≤ A → ∀ a : Fin r → L,
          (∀ n ∈ W, ∑ i, a i * x i n ∈ A) → ∀ n, ∑ i, a i * x i n ∈ A) ∧
      ∀ A : ValuationSubring L, O ≤ A.toSubring →
        ∃ (t : Fin r → ι → L) (M M' : Matrix (Fin r) (Fin r) L),
          (∀ j n, t j n = ∑ i, M j i * x i n) ∧ (∀ i n, x i n = ∑ j, M' i j * t j n) ∧
          (∀ j i, δ * M j i ∈ A) ∧ (∀ i j, M' i j ∈ A) ∧
          (∀ a : Fin r → L, (∀ n, ∑ j, a j * t j n ∈ A) → ∀ j, a j ∈ A) ∧
          ∃ ht : ∀ j n, t j n ∈ A,
            LinearIndependent (IsLocalRing.ResidueField A)
              (fun j => fun n : ι => IsLocalRing.residue A ⟨t j n, ht j n⟩) := by
  classical

  obtain ⟨W₀, hW₀⟩ := exists_window O x hO
  obtain ⟨c, hCunit⟩ := exists_pivots x hx
  set Cm : Matrix (Fin r) (Fin r) L := Matrix.of fun i k => x i (c k) with hCm
  set CmO : Matrix (Fin r) (Fin r) O := Matrix.of fun i k => ⟨x i (c k), hO i (c k)⟩ with hCmO
  have hCmO : Cm = O.subtype.mapMatrix CmO := by
    ext i k; rfl
  set δ : L := Cm.det with hδ
  have hδO : δ ∈ O := by
    rw [hδ, hCmO, ← RingHom.map_det]
    exact (CmO.det).2
  have hδunit : IsUnit δ := (Matrix.isUnit_iff_isUnit_det _).mp hCunit
  have hδ0 : δ ≠ 0 := hδunit.ne_zero
  have hadjO : ∀ l i, Cm.adjugate l i ∈ O := by
    intro l i
    rw [hCmO, ← RingHom.map_adjugate]
    exact (CmO.adjugate l i).2
  set W : Finset ι := W₀ ∪ Finset.univ.image c with hW
  have hcW : ∀ k, c k ∈ W := fun k =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem c (Finset.mem_univ k))

  have hwin : ∀ A : Subring L, O ≤ A → ∀ a : Fin r → L,
      (∀ n ∈ W, ∑ i, a i * x i n ∈ A) → ∀ n, ∑ i, a i * x i n ∈ A :=
    fun A hOA a ha n => window_property O x A hOA a
      (fun m hm => ha m (Finset.mem_union_left _ hm)) (hW := hW₀) n
  refine ⟨W, δ, hδO, hδ0, hwin, fun A hOA => ?_⟩

  let τ : (Fin r → L) →ₗ[L] (W → L) :=
    { toFun := fun a w => ∑ i, a i * x i (w : ι)
      map_add' := fun a b => by
        funext w; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun s a => by
        funext w; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hτ_apply : ∀ a (w : W), τ a w = ∑ i, a i * x i (w : ι) := fun a w => rfl
  have hτinj : Function.Injective τ := by
    intro a b hab
    have hvec : Function.Injective fun v : Fin r → L => Matrix.vecMul v Cm :=
      Matrix.vecMul_injective_iff_isUnit.mpr hCunit
    apply hvec
    funext k
    have h := congrFun hab ⟨c k, hcW k⟩
    simp only [hτ_apply] at h
    simp only [Matrix.vecMul, dotProduct, hCm, Matrix.of_apply]
    exact h
  set U : Submodule L (W → L) := LinearMap.range τ with hU
  have hUrank : Module.finrank L U = r := by
    rw [hU, LinearMap.finrank_range_of_inj hτinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

  obtain ⟨u, c', huU, huA, huc⟩ := gauss_elim A r U hUrank
  have hb : ∀ k, ∃ b : Fin r → L, τ b = u k := fun k => LinearMap.mem_range.mp (huU k)
  choose b hb using hb

  set t : Fin r → ι → L := fun k n => ∑ i, b k i * x i n with ht
  have htW : ∀ k (w : W), t k (w : ι) = u k w := by
    intro k w
    have h := congrFun (hb k) w
    rw [hτ_apply] at h
    exact h
  have htA : ∀ k n, t k n ∈ A := by
    intro k n
    exact hwin A.toSubring hOA (b k)
      (fun m hm => by show t k m ∈ A; rw [htW k ⟨m, hm⟩]; exact huA k _) n
  have htpiv : ∀ k l, t k (c' l : ι) = if k = l then 1 else 0 := fun k l => by rw [htW]; exact huc k l

  have hUzero : ∀ w ∈ U, (∀ l, w (c' l) = 0) → w = 0 := by
    intro w hwU hw0
    have hli : LinearIndependent L (fun k => (⟨u k, huU k⟩ : U)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg l
      have h := congrArg (fun z : U => (z : W → L) (c' l)) hg
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at h
      simp_rw [huc] at h
      simpa using h
    have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hUrank])
    have hmem : (⟨w, hwU⟩ : U) ∈ Submodule.span L (Set.range fun k => (⟨u k, huU k⟩ : U)) := by
      rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨g, hg⟩ := hmem
    have hg' : ∑ k, g k • u k = w := by
      have := congrArg (fun z : U => (z : W → L)) hg
      simpa using this
    have hg0 : ∀ l, g l = 0 := by
      intro l
      have h := congrFun hg' (c' l)
      rw [hw0 l] at h
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp_rw [huc] at h
      simpa using h
    rw [← hg']
    exact Finset.sum_eq_zero fun k _ => by rw [hg0 k, zero_smul]

  have hxM' : ∀ i n, x i n = ∑ k, x i (c' k : ι) * t k n := by
    intro i

    set a₀ : Fin r → L := (fun j => if j = i then 1 else 0) - ∑ k, x i (c' k : ι) • b k with ha₀
    have hτa₀ : τ a₀ = 0 := by
      refine hUzero _ (LinearMap.mem_range_self τ a₀) fun l => ?_
      rw [ha₀, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply]
      simp_rw [map_smul, Pi.smul_apply, hb, smul_eq_mul, huc]
      rw [hτ_apply]
      simp [Finset.sum_ite_eq', Finset.sum_ite_eq]
    have ha₀0 : a₀ = 0 := hτinj (by rw [hτa₀, map_zero])
    intro n
    have h := congrArg (fun a : Fin r → L => ∑ j, a j * x j n) ha₀0
    simp only [ha₀, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_eq_zero] at h
    rw [h, ht]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hδM : ∀ k i, δ * b k i ∈ A := by
    intro k i
    have hCinv : Invertible Cm := hCunit.invertible
    have hvec : Matrix.vecMul (b k) Cm = fun l => t k (c l) := by
      funext l
      simp only [Matrix.vecMul, dotProduct, hCm, Matrix.of_apply, ht]
    have hbk : b k = Matrix.vecMul (fun l => t k (c l)) Cm⁻¹ := by
      rw [← hvec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hCunit),
        Matrix.vecMul_one]
    have hinv : Cm⁻¹ = δ⁻¹ • Cm.adjugate := by
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [hbk, hinv]
    simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine sum_mem fun l _ => ?_
    have : δ * (t k (c l) * (δ⁻¹ * Cm.adjugate l i)) = t k (c l) * Cm.adjugate l i := by
      field_simp
    rw [this]
    exact mul_mem (htA k _) (hOA (hadjO l i))
  refine ⟨t, Matrix.of b, Matrix.of fun i k => x i (c' k : ι), fun k n => rfl,
    fun i n => hxM' i n, fun k i => hδM k i, fun i k => hOA (hO i _), ?_, htA, ?_⟩
  ·
    intro a ha l
    have h := ha (c' l : ι)
    simp_rw [htpiv] at h
    simpa using h
  ·
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h := congrFun hg (c' l : ι)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have hres : ∀ k, IsLocalRing.residue A ⟨t k (c' l : ι), htA k _⟩ = if k = l then 1 else 0 := by
      intro k
      have hval : (⟨t k (c' l : ι), htA k _⟩ : A) = if k = l then 1 else 0 := by
        apply Subtype.ext
        show t k (c' l : ι) = ((if k = l then 1 else 0 : A) : L)
        rw [htpiv]
        split_ifs <;> rfl
      rw [hval]
      split_ifs <;> simp
    simp_rw [hres] at h
    simpa using h

end Assembly

end WindowAdaptedBasisSol

theorem solution
    {L : Type*} [Field L] {ι : Type*} (O : Subring L) [IsNoetherianRing O] {r : ℕ}
    (x : Fin r → ι → L)
    (hx : ∀ a : Fin r → L, (∀ n, ∑ i, a i * x i n = 0) → ∀ i, a i = 0)
    (hO : ∀ i n, x i n ∈ O) :
    ∃ (W : Finset ι) (δ : L), δ ∈ O ∧ δ ≠ 0 ∧
      (∀ A : Subring L, O ≤ A → ∀ a : Fin r → L,
          (∀ n ∈ W, ∑ i, a i * x i n ∈ A) → ∀ n, ∑ i, a i * x i n ∈ A) ∧
      ∀ A : ValuationSubring L, O ≤ A.toSubring →
        ∃ (t : Fin r → ι → L) (M M' : Matrix (Fin r) (Fin r) L),
          (∀ j n, t j n = ∑ i, M j i * x i n) ∧ (∀ i n, x i n = ∑ j, M' i j * t j n) ∧
          (∀ j i, δ * M j i ∈ A) ∧ (∀ i j, M' i j ∈ A) ∧
          (∀ a : Fin r → L, (∀ n, ∑ j, a j * t j n ∈ A) → ∀ j, a j ∈ A) ∧
          ∃ ht : ∀ j n, t j n ∈ A,
            LinearIndependent (IsLocalRing.ResidueField A)
              (fun j => fun n : ι => IsLocalRing.residue A ⟨t j n, ht j n⟩) :=
  WindowAdaptedBasisSol.main O x hx hO

end S_ValuationSubring_exists_window_and_adapted_basis
end P2MW
export P2MW.S_ValuationSubring_exists_window_and_adapted_basis (solution)
