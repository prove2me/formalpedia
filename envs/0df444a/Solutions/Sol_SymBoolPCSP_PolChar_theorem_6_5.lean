-- Prove2me | solution 1 for SymBoolPCSP.PolChar.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T15:52:13.410743+00:00
-- url     : https://prove2.me/submissions/d9c16d14-dad3-4afd-9327-349b8c2e9145

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_PolChar_Basic

set_option autoImplicit false

namespace SymBoolPCSP.PolChar.Pf65

open PCSPBLPAff.Symmetric SymBoolPCSP.PolChar

theorem pol_proj {D τ : Type} {ar : τ → ℕ} (A B : RelStruct τ ar D) {L R : ℕ}
    (f : (Fin L → D) → D) (hf : IsPolymorphism A B f) (π : Fin L → Fin R) :
    IsPolymorphism A B (projection f π) := by
  intro S M hM
  exact hf S (fun l => M (π l)) (fun l => hM _)

theorem pol_id {D τ : Type} {ar : τ → ℕ} (A B : RelStruct τ ar D)
    (h : ∀ S, A.rel S ⊆ B.rel S) :
    IsPolymorphism A B (fun x : Fin 1 → D => x 0) := by
  intro S M hM
  exact h S (hM 0)

theorem pol_finit {D τ : Type} [Fintype D] [Fintype τ] {ar : τ → ℕ} (A B : RelStruct τ ar D) :
    ∃ N : ℕ, 0 < N ∧ ∀ L : ℕ, 0 < L → ∀ f : (Fin L → D) → D,
      (∀ π : Fin L → Fin N, IsPolymorphism A B (projection f π)) → IsPolymorphism A B f := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N, N = ∑ S : τ, Fintype.card (Fin (ar S) → D) + 1 := ⟨_, rfl⟩
  have hle : ∀ S : τ, Fintype.card (Fin (ar S) → D) ≤ N := by
    intro S
    have := Finset.single_le_sum (f := fun S : τ => Fintype.card (Fin (ar S) → D))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ S)
    omega
  refine ⟨N, by omega, ?_⟩
  intro L hL f hf S M hM
  let enc : (Fin (ar S) → D) → Fin N := fun t => Fin.castLE (hle S) (Fintype.equivFin _ t)
  have henc : Function.Injective enc := by
    intro a b h
    have h2 : Fintype.equivFin _ a = Fintype.equivFin _ b := Fin.castLE_injective (hle S) h
    exact (Fintype.equivFin _).injective h2
  let π : Fin L → Fin N := fun l => enc (M l)
  let Nm : Fin N → Fin (ar S) → D := fun r =>
    if h : ∃ l, enc (M l) = r then M (Classical.choose h) else M ⟨0, hL⟩
  have hNm : ∀ r, Nm r ∈ A.rel S := by
    intro r
    simp only [Nm]
    split_ifs <;> exact hM _
  have hcomp : ∀ l, Nm (π l) = M l := by
    intro l
    have h : ∃ l', enc (M l') = π l := ⟨l, rfl⟩
    show (if h : ∃ l', enc (M l') = π l then M (Classical.choose h) else M ⟨0, hL⟩) = M l
    rw [dif_pos h]
    exact henc (Classical.choose_spec h)
  have hres := hf π S Nm hNm
  have key : (fun c => projection f π (fun r => Nm r c)) = (fun c => f (fun l => M l c)) := by
    funext c
    simp only [projection, Function.comp_def, hcomp]
  rw [key] at hres
  exact hres

end SymBoolPCSP.PolChar.Pf65

open PCSPBLPAff.Symmetric SymBoolPCSP.PolChar in
theorem solution {D : Type} [Fintype D] [DecidableEq D] (F : FunFamily D) :
    (∃ (τ : Type) (_ : Fintype τ) (ar : τ → ℕ) (𝔸 𝔹 : RelStruct τ ar D),
        (∀ R : τ, 𝔸.rel R ⊆ 𝔹.rel R) ∧ ∀ L : ℕ, 0 < L → F L = Pol 𝔸 𝔹 L) ↔
      (ProjectionClosed F ∧ Finitizable F ∧ ContainsId F) := by
  constructor
  · rintro ⟨τ, hτ, ar, A, B, hsub, hF⟩
    refine ⟨?_, ?_, ?_⟩
    · intro L R hL hR f hf π
      rw [hF R hR]
      rw [hF L hL] at hf
      exact SymBoolPCSP.PolChar.Pf65.pol_proj A B f hf π
    · obtain ⟨N, hN, hfin⟩ := SymBoolPCSP.PolChar.Pf65.pol_finit A B
      refine ⟨N, hN, fun L hL f => ?_⟩
      rw [hF L hL]
      constructor
      · intro hf π
        rw [hF N hN]
        exact SymBoolPCSP.PolChar.Pf65.pol_proj A B f hf π
      · intro h
        apply hfin L hL f
        intro π
        have h2 := h π
        rw [hF N hN] at h2
        exact h2
    · show _ ∈ F 1
      rw [hF 1 Nat.one_pos]
      exact SymBoolPCSP.PolChar.Pf65.pol_id A B hsub
  · rintro ⟨hPC, ⟨R, hR, hfin⟩, hid⟩
    let e : (Fin R → D) ≃ Fin (Fintype.card (Fin R → D)) := Fintype.equivFin _
    refine ⟨Unit, inferInstance, fun _ => Fintype.card (Fin R → D),
      ⟨fun _ => {u | ∃ r : Fin R, u = fun i => e.symm i r}⟩,
      ⟨fun _ => {u | ∃ g ∈ F R, u = fun i => g (e.symm i)}⟩, ?_, ?_⟩
    · rintro - u ⟨r, rfl⟩
      exact ⟨projection (fun x : Fin 1 → D => x 0) (fun _ => r),
        hPC 1 R Nat.one_pos hR _ hid _, rfl⟩
    · intro L hL
      ext f
      rw [hfin L hL f]
      constructor
      · intro h S M hM
        choose π hπ using hM
        refine ⟨projection f π, h π, ?_⟩
        funext c
        simp only [projection, Function.comp_def]
        congr 1
        funext l
        rw [hπ l]
      · intro h π
        obtain ⟨g, hg, hfg⟩ := h () (fun l => fun i => e.symm i (π l)) (fun l => ⟨π l, rfl⟩)
        have hpg : projection f π = g := by
          funext y
          have h3 := congrFun hfg (e y)
          simpa [projection, Function.comp_def] using h3
        rw [hpg]
        exact hg
