-- Prove2me | solution 1 for PCSPBLPAff.Characterization.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:59:33.197451+00:00
-- url     : https://prove2.me/submissions/c849f48d-4a9e-41bf-9ef5-b12293eb6c59

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

open PCSPBLPAff.Symmetric

namespace PCSPBLPAff.Characterization.L17aux

/-- generic fibre sum (the common body of `minorQ` / `minorZ`). -/
def fs {ι κ M : Type} [Fintype ι] [DecidableEq κ] [AddCommMonoid M] (π : ι → κ) (w : ι → M) :
    κ → M :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j => π j = i), w j

theorem minorQ_eq_fs {ι κ : Type} [Fintype ι] [DecidableEq κ] (π : ι → κ) (w : ι → ℚ) :
    minorQ π w = fs π w := rfl

theorem minorZ_eq_fs {ι κ : Type} [Fintype ι] [DecidableEq κ] (π : ι → κ) (w : ι → ℤ) :
    minorZ π w = fs π w := rfl

theorem fs_comp {ι κ μ M : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq μ]
    [AddCommMonoid M] (π : ι → κ) (ρ : κ → μ) (w : ι → M) :
    fs ρ (fs π w) = fs (ρ ∘ π) w := by
  funext m
  simp only [fs, Finset.sum_filter, Function.comp]
  calc _ = ∑ k, ∑ j, (if π j = k then (if ρ k = m then w j else 0) else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> simp
    _ = ∑ j, ∑ k, (if π j = k then (if ρ k = m then w j else 0) else 0) := Finset.sum_comm
    _ = _ := by refine Finset.sum_congr rfl fun j _ => ?_; simp

theorem fs_equiv {ι ι' κ M : Type} [Fintype ι] [Fintype ι'] [DecidableEq κ] [AddCommMonoid M]
    (g : ι ≃ ι') (φ : ι → κ) (w : ι → M) :
    fs (φ ∘ g.symm) (w ∘ g.symm) = fs φ w := by
  funext i
  simp only [fs, Finset.sum_filter, Function.comp]
  exact Fintype.sum_equiv g.symm _ _ (fun _ => rfl)

theorem fs_subtype {ι κ M : Type} [Fintype ι] [DecidableEq κ] [AddCommMonoid M]
    (P : ι → Prop) [Fintype (Subtype P)] (φ : ι → κ) (w : ι → M) (hw : ∀ y, ¬ P y → w y = 0) :
    fs (φ ∘ (Subtype.val : Subtype P → ι)) (w ∘ Subtype.val) = fs φ w := by
  classical
  funext i
  simp only [fs, Finset.sum_filter, Function.comp]
  rw [← Finset.sum_subtype (p := P) (Finset.univ.filter P) (by simp)
    (fun y => if φ y = i then w y else 0)]
  apply Finset.sum_filter_of_ne
  intro y _ hy
  by_contra hP
  exact hy (by simp [hw y hP])

theorem isBLPAffObj_minor {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (π : ι → κ)
    {w : ι → ℚ} {r : ι → ℤ} (h : IsBLPAffObj w r) :
    IsBLPAffObj (minorQ π w) (minorZ π r) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨fun i => Finset.sum_nonneg fun j _ => h0 j, ?_, ?_, fun i hi => ?_⟩
  · unfold minorQ; rw [Finset.sum_fiberwise]; exact h1
  · unfold minorZ; rw [Finset.sum_fiberwise]; exact h2
  · unfold minorZ
    unfold minorQ at hi
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h0 j)] at hi
    exact Finset.sum_eq_zero fun j hj => h3 j (hi j hj)

end PCSPBLPAff.Characterization.L17aux

open PCSPBLPAff.Characterization PCSPBLPAff.Characterization.L17aux in
theorem PCSPBLPAff.Characterization.lemma_17_main {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) :
    (∃ σ : FreeDom A → B, PCSPBLPAff.Symmetric.IsHom (freeStruct 𝔸) 𝔹 σ) ↔ HasMinionHomToPol 𝔸 𝔹 := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun L x a => σ ⟨(minorQ a x.1.1, minorZ a x.1.2), isBLPAffObj_minor a x.2⟩,
      fun L x => ⟨?_, ?_⟩⟩
    · intro R M hM
      let t : Fin (ar R) → FreeDom A := fun c =>
        ⟨(minorQ (fun l => M l c) x.1.1, minorZ (fun l => M l c) x.1.2),
          isBLPAffObj_minor _ x.2⟩
      have ht : t ∈ (freeStruct 𝔸).rel R := by
        refine ⟨minorQ M x.1.1, minorZ M x.1.2, isBLPAffObj_minor M x.2, ?_, ?_⟩
        · intro y hy
          refine Finset.sum_eq_zero fun l hl => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
          exact absurd (hl ▸ hM l) hy
        · intro k
          simp only [t, minorQ_eq_fs, minorZ_eq_fs, fs_comp]
          rfl
      exact hσ R t ht
    · intro L' π h
      funext a
      simp only [polMinor]
      congr 1
      apply Subtype.ext
      simp only [minorQ_eq_fs, minorZ_eq_fs, fs_comp]
  · rintro ⟨ξ, hξ⟩
    classical
    let n := Fintype.card A
    let e : A ≃ Fin n := Fintype.equivFin A
    refine ⟨fun x => ξ n ⟨(minorQ e x.1.1, minorZ e x.1.2), isBLPAffObj_minor e x.2⟩
      (fun i => e.symm i), ?_⟩
    intro R t ⟨p, q, hpq, hvan, hmarg⟩
    let S := {y : Fin (ar R) → A // y ∈ 𝔸.rel R}
    let m := Fintype.card S
    let g : S ≃ Fin m := Fintype.equivFin S
    have qvan : ∀ y, y ∉ 𝔸.rel R → q y = 0 := fun y hy => hpq.2.2.2 y (hvan y hy)
    have hz : IsBLPAffObj (p ∘ Subtype.val ∘ g.symm) (q ∘ Subtype.val ∘ g.symm) := by
      obtain ⟨h0, h1, h2, h3⟩ := hpq
      refine ⟨fun l => h0 _, ?_, ?_, fun l hl => h3 _ hl⟩
      · rw [show (∑ l, (p ∘ Subtype.val ∘ g.symm) l) = ∑ s : S, p s.1 from
            Fintype.sum_equiv g.symm _ _ (fun _ => rfl)]
        rw [← Finset.sum_subtype (p := fun y => y ∈ 𝔸.rel R)
          (Finset.univ.filter (fun y => y ∈ 𝔸.rel R)) (by simp) p]
        rw [Finset.sum_filter_of_ne (fun y _ hy => by_contra fun h => hy (hvan y h))]
        exact h1
      · rw [show (∑ l, (q ∘ Subtype.val ∘ g.symm) l) = ∑ s : S, q s.1 from
            Fintype.sum_equiv g.symm _ _ (fun _ => rfl)]
        rw [← Finset.sum_subtype (p := fun y => y ∈ 𝔸.rel R)
          (Finset.univ.filter (fun y => y ∈ 𝔸.rel R)) (by simp) q]
        rw [Finset.sum_filter_of_ne (fun y _ hy => by_contra fun h => hy (qvan y h))]
        exact h2
    let z : BLPAffObj (Fin m) := ⟨(p ∘ Subtype.val ∘ g.symm, q ∘ Subtype.val ∘ g.symm), hz⟩
    have hpol := (hξ m z).1 R (fun l => (g.symm l).1) (fun l => (g.symm l).2)
    convert hpol using 1
    funext c
    let πc : Fin m → Fin n := fun l => e ((g.symm l).1 c)
    have key : (⟨(minorQ e (t c).1.1, minorZ e (t c).1.2), isBLPAffObj_minor e (t c).2⟩ :
        BLPAffObj (Fin n)) = ⟨(minorQ πc z.1.1, minorZ πc z.1.2), isBLPAffObj_minor πc z.2⟩ := by
      apply Subtype.ext
      change (minorQ e (t c).val.1, minorZ e (t c).val.2) =
        (minorQ (((e ∘ fun y => y c) ∘ Subtype.val) ∘ g.symm) ((p ∘ Subtype.val) ∘ g.symm),
         minorZ (((e ∘ fun y => y c) ∘ Subtype.val) ∘ g.symm) ((q ∘ Subtype.val) ∘ g.symm))
      rw [hmarg c]
      simp only [minorQ_eq_fs, minorZ_eq_fs, fs_comp, fs_equiv]
      rw [fs_subtype (fun y => y ∈ 𝔸.rel R) _ _ hvan, fs_subtype (fun y => y ∈ 𝔸.rel R) _ _ qvan]
    simp only [Function.comp_apply]
    rw [key, (hξ m z).2 n πc]
    simp only [polMinor]
    congr 1
    funext l
    simp [πc]

open PCSPBLPAff.Characterization in
/-- Lemma 17 ([BBKO19, Lemma 4.4]) for `M = M_BLP+Aff`. -/
theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    (∃ σ : FreeDom A → B, PCSPBLPAff.Symmetric.IsHom (freeStruct 𝔸) 𝔹 σ) ↔ HasMinionHomToPol 𝔸 𝔹 :=
  PCSPBLPAff.Characterization.lemma_17_main 𝔸 𝔹
