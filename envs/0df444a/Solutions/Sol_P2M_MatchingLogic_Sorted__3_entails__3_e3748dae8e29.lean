-- Prove2me | solution 1 for P2M_MatchingLogic_Sorted__3_entails__3_e3748dae8e29
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:41.787118+00:00
-- url     : https://prove2.me/submissions/2edeccad-f0cd-42cb-b935-5b6d18ca8302

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Theorems.Thm_MatchingLogic_Sorted_mdenote_al
public import Theorems.Thm_MatchingLogic_Sorted_MModel_app_eq_empty

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}
namespace MatchingLogic.Sorted
theorem _root_.solution (x y : Var) (hxy : x ≠ y) :
    MGlobalCons (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) := by
  classical
  intro M hΓ
  have hγ : M.Sat (MPattern.al x Srt3.b (MPattern.al y Srt3.b
      (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
        (MPattern.var (S := S3) y Srt3.b))))) :=
    hΓ _ (Set.mem_singleton _)
  let ρ0 : MVal M Var := fun t _ => Classical.choice (M.nonempty t)
  have hb : ∀ r s : M.carrier Srt3.b, r = s := by
    intro r s
    by_contra hrs
    let ρrs : MVal M Var := mupdate M (mupdate M ρ0 Srt3.b x r) Srt3.b y s
    have houter := hγ ρ0
    rw [mdenote_al] at houter
    have hx : mdenote M (mupdate M ρ0 Srt3.b x r)
        (MPattern.al y Srt3.b
          (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
            (MPattern.var (S := S3) y Srt3.b)))) = Set.univ := by
      ext u
      constructor
      · intro _
        trivial
      · intro _
        have hu : u ∈ ⋂ a : M.carrier Srt3.b,
            mdenote M (mupdate M ρ0 Srt3.b x a)
              (MPattern.al y Srt3.b
                (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
                  (MPattern.var (S := S3) y Srt3.b)))) := by
          rw [houter]
          trivial
        exact Set.mem_iInter.mp hu r
    rw [mdenote_al] at hx
    have hinner : mdenote M ρrs
        (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b))) = Set.univ := by
      ext u
      constructor
      · intro _
        trivial
      · intro _
        have hu : u ∈ ⋂ a : M.carrier Srt3.b,
            mdenote M
              (mupdate M (mupdate M ρ0 Srt3.b x r) Srt3.b y a)
              (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
                (MPattern.var (S := S3) y Srt3.b))) := by
          rw [hx]
          trivial
        exact Set.mem_iInter.mp hu s
    have hand : mdenote M ρrs
        (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b)) = ∅ := by
      ext u
      simp [ρrs, mdenote, mupdate, hxy, hrs]
    have happ : mdenote M ρrs
        (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b))) = ∅ := by
      apply MModel.app_eq_empty M Sym3.f _ ⟨0, Nat.zero_lt_one⟩
      exact hand
    have u : M.carrier Srt3.a := Classical.choice (M.nonempty Srt3.a)
    have hu : u ∈ mdenote M ρrs
        (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
          (MPattern.var (S := S3) y Srt3.b))) := by
      rw [hinner]
      trivial
    rw [happ] at hu
    exact hu
  intro ρ
  have hiff : ∀ ρ' : MVal M Var,
      mdenote M ρ'
        (MPattern.iff (gAp (MPattern.var (S := S3) x Srt3.b))
          (gAp (MPattern.var (S := S3) y Srt3.b))) = Set.univ := by
    intro ρ'
    have hval : ρ' Srt3.b x = ρ' Srt3.b y := hb _ _
    ext u
    simp [mdenote, hval]
  rw [mdenote_al]
  apply Set.eq_univ_of_forall
  intro u
  simp only [Set.mem_iInter]
  intro r
  rw [mdenote_al]
  simp only [Set.mem_iInter]
  intro s
  rw [hiff]
  trivial
end MatchingLogic.Sorted
