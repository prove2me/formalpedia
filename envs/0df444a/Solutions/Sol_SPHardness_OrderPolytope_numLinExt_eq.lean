-- Prove2me | solution 1 for SPHardness.OrderPolytope.numLinExt_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:26:02.334774+00:00
-- url     : https://prove2.me/submissions/6cd6254c-b662-4d08-b7b9-3d181df4cb82

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

set_option autoImplicit false
open SPHardness.OrderPolytope MeasureTheory

section S_lin
variable {P : Type} [Fintype P]

lemma S_sort (ξ : P → ℝ) :
    ∃ e : P ≃ Fin (Fintype.card P), ∀ a b, e a ≤ e b → ξ a ≤ ξ b := by
  classical
  let f : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let key : P → ℝ ×ₗ Fin (Fintype.card P) := fun a => toLex (ξ a, f a)
  have hinj : Function.Injective key := by
    intro a b h
    have := congrArg (fun z => (ofLex z).2) h
    exact f.injective this
  let _ : LinearOrder P := LinearOrder.lift' key hinj
  let o : P ≃o Fin (Fintype.card P) := (Fintype.orderIsoFinOfCardEq P rfl).symm
  refine ⟨o.toEquiv, fun a b hab => ?_⟩
  have h1 : a ≤ b := o.le_iff_le.mp hab
  have h2 : key a ≤ key b := h1
  rcases Prod.Lex.le_iff.mp h2 with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

lemma S_strict (ξ : P → ℝ) (hξ : Function.Injective ξ) (e : P ≃ Fin (Fintype.card P))
    (h : ∀ a b, e a ≤ e b → ξ a ≤ ξ b) : ∀ a b, e a < e b ↔ ξ a < ξ b := by
  intro a b
  constructor
  · intro hab
    have h1 := h a b hab.le
    refine lt_of_le_of_ne h1 (fun heq => ?_)
    have := hξ heq
    subst this
    exact lt_irrefl _ hab
  · intro hab
    by_contra hcon
    have : e b ≤ e a := not_lt.mp hcon
    have := h b a this
    linarith

lemma S_unique (ξ : P → ℝ) (hξ : Function.Injective ξ) (e e' : P ≃ Fin (Fintype.card P))
    (h : ∀ a b, e a ≤ e b → ξ a ≤ ξ b) (h' : ∀ a b, e' a ≤ e' b → ξ a ≤ ξ b) : e = e' := by
  have k := S_strict ξ hξ e h
  have k' := S_strict ξ hξ e' h'
  have hmono : StrictMono (fun i : Fin (Fintype.card P) => e' (e.symm i)) := by
    intro i j hij
    have : e (e.symm i) < e (e.symm j) := by simpa using hij
    exact (k' _ _).mpr ((k _ _).mp this)
  have hid : StrictMono (fun i : Fin (Fintype.card P) => i) := fun i j h => h
  have hrange : Set.range (fun i : Fin (Fintype.card P) => e' (e.symm i)) =
      Set.range (fun i : Fin (Fintype.card P) => i) := by
    ext j
    simp only [Set.mem_range]
    exact ⟨fun _ => ⟨j, rfl⟩, fun _ => ⟨e.symm.trans e' |>.symm j, by simp⟩⟩
  have hfun := (StrictMono.range_inj hmono hid).mp hrange
  refine Equiv.ext fun a => ?_
  have := congrFun hfun (e a)
  simpa using this.symm
end S_lin

def S_C (P : Type) [Fintype P] (e : P ≃ Fin (Fintype.card P)) : Set (P → ℝ) :=
  {ξ | ξ ∈ cube P ∧ ∀ a b, e a ≤ e b → ξ a ≤ ξ b}

section S_vol
variable {P : Type} [Fintype P]

lemma S_cube_meas : MeasurableSet (cube P) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma S_C_meas (e : P ≃ Fin (Fintype.card P)) : MeasurableSet (S_C P e) := by
  have : S_C P e = cube P ∩ ⋂ a, ⋂ b, ⋂ (_ : e a ≤ e b), {ξ : P → ℝ | ξ a ≤ ξ b} := by
    ext ξ; simp [S_C]
  rw [this]
  exact S_cube_meas.inter (MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b))

lemma S_C_vol (e e' : P ≃ Fin (Fintype.card P)) : volume (S_C P e) = volume (S_C P e') := by
  let ρ : P ≃ P := e.trans e'.symm
  let T : (P → ℝ) ≃ᵐ (P → ℝ) := MeasurableEquiv.arrowCongr' ρ (MeasurableEquiv.refl ℝ)
  have hT : MeasureTheory.MeasurePreserving T volume volume :=
    volume_preserving_arrowCongr' ρ (MeasurableEquiv.refl ℝ) (MeasureTheory.MeasurePreserving.id volume)
  have hTapp : ∀ (ξ : P → ℝ) (i : P), T ξ i = ξ (ρ.symm i) := fun ξ i => rfl
  have hρ : ∀ i, e (ρ.symm i) = e' i := by intro i; simp [ρ]
  have hρ' : ∀ i, e' (ρ i) = e i := by intro i; simp [ρ]
  have hset : S_C P e = T ⁻¹' (S_C P e') := by
    ext ξ
    simp only [Set.mem_preimage, S_C, Set.mem_setOf_eq, cube, Set.mem_pi, Set.mem_univ,
      true_implies, hTapp]
    constructor
    · rintro ⟨hc, ho⟩
      refine ⟨fun i => hc _, fun a b hab => ho _ _ ?_⟩
      rw [hρ, hρ]; exact hab
    · rintro ⟨hc, ho⟩
      refine ⟨fun i => ?_, fun a b hab => ?_⟩
      · simpa using hc (ρ i)
      · have := ho (ρ a) (ρ b) (by rw [hρ', hρ']; exact hab)
        simpa using this
  rw [hset, hT.measure_preimage_equiv]

lemma S_hyp_null (a b : P) (hab : a ≠ b) : volume {ξ : P → ℝ | ξ a = ξ b} = 0 := by
  classical
  let s : Submodule ℝ (P → ℝ) :=
    LinearMap.ker ((LinearMap.proj a : (P → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj b)
  have hs : s ≠ ⊤ := by
    intro h
    have : (Pi.single a (1 : ℝ) : P → ℝ) ∈ s := by rw [h]; trivial
    simp [s, Pi.single_eq_of_ne hab.symm] at this
  have h0 := MeasureTheory.Measure.addHaar_submodule (volume : Measure (P → ℝ)) s hs
  have hset : {ξ : P → ℝ | ξ a = ξ b} = (s : Set (P → ℝ)) := by
    ext ξ; simp [s, sub_eq_zero]
  rw [hset]; exact h0

lemma S_noninj_null : volume {ξ : P → ℝ | ¬ Function.Injective ξ} = 0 := by
  have hsub : {ξ : P → ℝ | ¬ Function.Injective ξ} ⊆
      ⋃ p : {p : P × P // p.1 ≠ p.2}, {ξ : P → ℝ | ξ p.1.1 = ξ p.1.2} := by
    intro ξ hξ
    simp only [Function.Injective, not_forall] at hξ
    obtain ⟨a, b, hab, hne⟩ := hξ
    exact Set.mem_iUnion.mpr ⟨⟨(a, b), hne⟩, hab⟩
  exact measure_mono_null hsub (measure_iUnion_null fun p => S_hyp_null _ _ p.2)

lemma S_C_inter_null (e e' : P ≃ Fin (Fintype.card P)) (hne : e ≠ e') :
    volume (S_C P e ∩ S_C P e') = 0 := by
  refine measure_mono_null (fun ξ hξ => ?_) S_noninj_null
  intro hinj
  exact hne (S_unique ξ hinj e e' hξ.1.2 hξ.2.2)

lemma S_cover : cube P = ⋃ e : P ≃ Fin (Fintype.card P), S_C P e := by
  ext ξ
  simp only [Set.mem_iUnion]
  constructor
  · intro hξ
    obtain ⟨e, he⟩ := S_sort ξ
    exact ⟨e, hξ, he⟩
  · rintro ⟨e, he, -⟩
    exact he

lemma S_cube_vol : volume (cube P) = 1 := by
  unfold cube
  rw [volume_pi_pi]
  simp

end S_vol

open scoped Nat in
theorem S_numLinExt_eq (P : Type) [Fintype P] [PartialOrder P] :
    (numLinExt P : ℝ) = ((Fintype.card P)! : ℝ) * volOrder P := by
  classical
  let n := Fintype.card P
  let c : ENNReal := volume (S_C P (Fintype.equivFin P))
  have hc : ∀ e, volume (S_C P e) = c := fun e => S_C_vol e _
  -- pairwise a.e.-disjointness
  have hdisj : ∀ s : Finset (P ≃ Fin n),
      Set.Pairwise (↑s) (Function.onFun (AEDisjoint volume) (fun e => S_C P e)) := by
    intro s e _ e' _ hne
    exact S_C_inter_null e e' hne
  have hmeas : ∀ e : P ≃ Fin n, NullMeasurableSet (S_C P e) volume :=
    fun e => (S_C_meas e).nullMeasurableSet
  -- n! * c = 1
  have hsum : (1 : ENNReal) = ((Nat.factorial n : ℕ) : ENNReal) * c := by
    have h1 := measure_biUnion_finset₀ (μ := (volume : Measure (P → ℝ))) (s := Finset.univ)
      (f := fun e : P ≃ Fin n => S_C P e) (hdisj _) (fun e _ => hmeas e)
    have h2 : (⋃ e ∈ (Finset.univ : Finset (P ≃ Fin n)), S_C P e) = cube P := by
      rw [S_cover]; simp only [Finset.mem_univ, Set.iUnion_true]
      try rfl
    rw [h2, S_cube_vol] at h1
    rw [h1, Finset.sum_congr rfl (fun e _ => hc e), Finset.sum_const, Finset.card_univ,
      Fintype.card_equiv (Fintype.equivFin P), nsmul_eq_mul]
  have hsumR : ((Nat.factorial n : ℕ) : ℝ) * c.toReal = 1 := by
    have := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_mul] at this
    simpa using this.symm
  -- the linear extensions
  set Sset := FCP.Order.LinearExtensions P with hSset
  let Sfin : Finset (P ≃ Fin n) := Sset.toFinset
  have hcard : numLinExt P = Sfin.card := by
    unfold numLinExt
    exact Set.ncard_eq_toFinset_card' Sset
  have hSmem : ∀ e, e ∈ Sfin ↔ ∀ x y : P, x ≤ y → e x ≤ e y := by
    intro e; simp only [Sfin, Set.mem_toFinset]; exact Iff.rfl
  -- the order polytope is a.e. the union of chambers of linear extensions
  have hO1 : (⋃ e ∈ Sfin, S_C P e) ⊆ orderPolytope P := by
    intro ξ hξ
    simp only [Set.mem_iUnion] at hξ
    obtain ⟨e, he, hc', ho⟩ := hξ
    refine ⟨hc', fun i j hij => ho i j ((hSmem e).mp he i j hij)⟩
  have hO2 : orderPolytope P ⊆ (⋃ e ∈ Sfin, S_C P e) ∪ {ξ : P → ℝ | ¬ Function.Injective ξ} := by
    intro ξ hξ
    by_cases hinj : Function.Injective ξ
    · left
      obtain ⟨e, he⟩ := S_sort ξ
      have hmon : ∀ x y : P, x ≤ y → e x ≤ e y := by
        intro x y hxy
        by_contra hcon
        have hlt : e y < e x := not_le.mp hcon
        have := (S_strict ξ hinj e he y x).mp hlt
        have := hξ.2 x y hxy
        linarith
      simp only [Set.mem_iUnion]
      exact ⟨e, (hSmem e).mpr hmon, hξ.1, he⟩
    · right; exact hinj
  have hvolO : volume (orderPolytope P) = ∑ e ∈ Sfin, volume (S_C P e) := by
    apply le_antisymm
    · calc volume (orderPolytope P)
          ≤ volume ((⋃ e ∈ Sfin, S_C P e) ∪ {ξ : P → ℝ | ¬ Function.Injective ξ}) := measure_mono hO2
        _ ≤ volume (⋃ e ∈ Sfin, S_C P e) + volume {ξ : P → ℝ | ¬ Function.Injective ξ} :=
            measure_union_le _ _
        _ = ∑ e ∈ Sfin, volume (S_C P e) := by
            rw [S_noninj_null, add_zero]
            exact measure_biUnion_finset₀ (hdisj Sfin) (fun e _ => hmeas e)
    · calc ∑ e ∈ Sfin, volume (S_C P e) = volume (⋃ e ∈ Sfin, S_C P e) :=
            (measure_biUnion_finset₀ (hdisj Sfin) (fun e _ => hmeas e)).symm
        _ ≤ volume (orderPolytope P) := measure_mono hO1
  have hvolR : volOrder P = (Sfin.card : ℝ) * c.toReal := by
    unfold volOrder
    rw [hvolO, Finset.sum_congr rfl (fun e _ => hc e), Finset.sum_const, nsmul_eq_mul,
      ENNReal.toReal_mul]
    simp
  rw [hcard, hvolR]
  have : ((Nat.factorial n : ℕ) : ℝ) * ((Sfin.card : ℝ) * c.toReal) = Sfin.card := by
    calc ((Nat.factorial n : ℕ) : ℝ) * ((Sfin.card : ℝ) * c.toReal)
        = (Sfin.card : ℝ) * (((Nat.factorial n : ℕ) : ℝ) * c.toReal) := by ring
      _ = Sfin.card := by rw [hsumR, mul_one]
  exact this.symm

open scoped Nat in
theorem solution (P : Type) [Fintype P] [PartialOrder P] :
    (numLinExt P : ℝ) = ((Fintype.card P)! : ℝ) * volOrder P := S_numLinExt_eq P
