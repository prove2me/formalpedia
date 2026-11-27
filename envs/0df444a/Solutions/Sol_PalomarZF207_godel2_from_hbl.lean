-- Prove2me | solution 1 for PalomarZF207.godel2_from_hbl
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-27T00:03:26.721274+00:00
-- url     : https://prove2.me/submissions/930dddb8-db5b-4694-8353-2be59f0315e2

import Definitions.Def_palomar_zf207_zf

open PalomarZF207

namespace SolGodel2HBL

private theorem prov_mp {a b : Formula} (hab : Provable (.imp a b)) (ha : Provable a) : Provable b := by
  rcases hab with ⟨Γ₁, hAx₁, d₁⟩
  rcases ha with ⟨Γ₂, hAx₂, d₂⟩
  refine ⟨Γ₁ ++ Γ₂, fun q hq => ?_, ?_⟩
  · rcases List.mem_append.mp hq with h1 | h2
    · exact hAx₁ q h1
    · exact hAx₂ q h2
  · exact ND.ie (ND.wk (fun q hq => List.mem_append_left Γ₂ hq) d₁)
                (ND.wk (fun q hq => List.mem_append_right Γ₁ hq) d₂)

private theorem prov_iff_mp {a b : Formula} (h : Provable (sourceIff a b)) : Provable (.imp a b) := by
  rcases h with ⟨Γ, hAx, d⟩
  exact ⟨Γ, hAx, ND.ce1 d⟩

private theorem prov_iff_mpr {a b : Formula} (h : Provable (sourceIff a b)) : Provable (.imp b a) := by
  rcases h with ⟨Γ, hAx, d⟩
  exact ⟨Γ, hAx, ND.ce2 d⟩

private theorem prov_contrapose {a b : Formula} (h : Provable (.imp a b)) :
    Provable (.imp (Neg b) (Neg a)) := by
  rcases h with ⟨Γ, hAx, d⟩
  refine ⟨Γ, hAx, ND.ii (ND.ii ?_)⟩
  have d' : ND (.seq (a :: Neg b :: Γ) (.imp a b)) :=
    ND.wk (fun q hq => .tail _ (.tail _ hq)) d
  have hb : ND (.seq (a :: Neg b :: Γ) b) := ND.ie d' (ND.ctx (.head _))
  exact ND.ie (ND.ctx (.tail _ (.head _))) hb

private theorem prov_combine_3 {a b c d : Formula}
    (h1 : Provable (.imp a b))
    (h2 : Provable (.imp b (.imp c d)))
    (h3 : Provable (.imp a c)) :
    Provable (.imp a d) := by
  rcases h1 with ⟨Γ₁, hAx₁, d₁⟩
  rcases h2 with ⟨Γ₂, hAx₂, d₂⟩
  rcases h3 with ⟨Γ₃, hAx₃, d₃⟩
  let Γ := Γ₁ ++ Γ₂ ++ Γ₃
  have hAx : ∀ q, q ∈ Γ → Axiom q := by
    intro q hq
    rcases List.mem_append.mp hq with h12 | h3'
    · rcases List.mem_append.mp h12 with h1' | h2'
      · exact hAx₁ q h1'
      · exact hAx₂ q h2'
    · exact hAx₃ q h3'
  refine ⟨Γ, hAx, ND.ii ?_⟩
  have d₁' : ND (.seq (a :: Γ) (.imp a b)) :=
    ND.wk (fun q hq => .tail _ (List.mem_append_left Γ₃ (List.mem_append_left Γ₂ hq))) d₁
  have d₂' : ND (.seq (a :: Γ) (.imp b (.imp c d))) :=
    ND.wk (fun q hq => .tail _ (List.mem_append_left Γ₃ (List.mem_append_right Γ₁ hq))) d₂
  have d₃' : ND (.seq (a :: Γ) (.imp a c)) :=
    ND.wk (fun q hq => .tail _ (List.mem_append_right (Γ₁ ++ Γ₂) hq)) d₃
  have ha : ND (.seq (a :: Γ) a) := ND.ctx (.head _)
  have hb : ND (.seq (a :: Γ) b) := ND.ie d₁' ha
  have hc : ND (.seq (a :: Γ) c) := ND.ie d₃' ha
  exact ND.ie (ND.ie d₂' hb) hc

end SolGodel2HBL

theorem solution
    (Box : Formula → Formula)
    (hClosed : ∀ φ, Closed φ → Closed (Box φ))
    (hD1 : ∀ φ, Closed φ → Provable φ → Provable (Box φ))
    (hD2 : ∀ φ ψ, Closed φ → Closed ψ → Provable (.imp (Box (.imp φ ψ)) (.imp (Box φ) (Box ψ))))
    (hD3 : ∀ φ, Closed φ → Provable (.imp (Box φ) (Box (Box φ))))
    (hDiag : ∃ G, Closed G ∧ Provable (sourceIff G (Neg (Box G)))) :
    Consistent → ¬ Provable (Neg (Box .bot)) := by
  intro hCon hNegBoxBot
  obtain ⟨G, hGcl, hGiff⟩ := hDiag
  have hBGcl : Closed (Box G) := hClosed G hGcl
  have hNBGcl : Closed (Neg (Box G)) := ⟨hBGcl, trivial⟩
  have h1 : Provable (.imp G (Neg (Box G))) := SolGodel2HBL.prov_iff_mp hGiff
  have h2 : Provable (Box (.imp G (Neg (Box G)))) := hD1 _ ⟨hGcl, hNBGcl⟩ h1
  have h3 : Provable (.imp (Box G) (Box (Neg (Box G)))) :=
    SolGodel2HBL.prov_mp (hD2 G (Neg (Box G)) hGcl hNBGcl) h2
  have h4 : Provable (.imp (Box (Neg (Box G))) (.imp (Box (Box G)) (Box .bot))) :=
    hD2 (Box G) .bot hBGcl trivial
  have h5 : Provable (.imp (Box G) (Box (Box G))) := hD3 G hGcl
  have h6 : Provable (.imp (Box G) (Box .bot)) := SolGodel2HBL.prov_combine_3 h3 h4 h5
  have h7 : Provable (.imp (Neg (Box .bot)) (Neg (Box G))) := SolGodel2HBL.prov_contrapose h6
  have h8 : Provable (Neg (Box G)) := SolGodel2HBL.prov_mp h7 hNegBoxBot
  have h9 : Provable G := SolGodel2HBL.prov_mp (SolGodel2HBL.prov_iff_mpr hGiff) h8
  have h10 : Provable (Box G) := hD1 G hGcl h9
  exact hCon (SolGodel2HBL.prov_mp h8 h10)
